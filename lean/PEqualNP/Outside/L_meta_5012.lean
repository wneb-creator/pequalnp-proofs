import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5012





open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity

lemma replacement_isLeastAO {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C D : Circuit} (hC : IsLeastAO G C) (hD : IsAO2 n D)
    (hfun : circuitFun n D = NestedCover.graphFun G ∅) (hsize : D.size ≤ C.size) :
    IsLeastAO G D := by
  refine ⟨hD, hfun, ?_⟩
  intro E hE hEfun
  exact hsize.trans (hC.2.2 E hE hEfun)

lemma replacement_size_eq {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C D : Circuit} (hC : IsLeastAO G C) (hD : IsAO2 n D)
    (hfun : circuitFun n D = NestedCover.graphFun G ∅) (hsize : D.size ≤ C.size) :
    D.size = C.size :=
  Nat.le_antisymm hsize (hC.2.2 D hD hfun)

lemma replacement_junk_ne_one
    (hfirst : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (s : Fin n → Bool),
      (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → NoFourCycle G → IsLeastAO G C →
      (junk G C).card ≠ 1)
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C D : Circuit}
    (s : Fin n → Bool) (hs : ∀ u v : Fin n, G.Adj u v → s u ≠ s v)
    (hfour : NoFourCycle G) (hC : IsLeastAO G C) (hD : IsAO2 n D)
    (hfun : circuitFun n D = NestedCover.graphFun G ∅) (hsize : D.size ≤ C.size) :
    (junk G D).card ≠ 1 :=
  hfirst n G D s hs hfour (replacement_isLeastAO hC hD hfun hsize)

lemma junk_card_le_size {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) : (junk G C).card ≤ C.size := by
  simpa only [junk, gatesWhere, Circuit.size, Finset.card_range] using
    Finset.card_filter_le (Finset.range C.gates.length)
      (fun j => PEqualNP.CleanedNonEdge.IsDirtyAnd n G C j)

lemma edge_exists_of_nonempty_junk {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hC : IsLeastAO G C) (hj : (junk G C).Nonempty) :
    ∃ u v : Fin n, G.Adj u v := by
  by_contra hnone
  have hn : ∀ u v : Fin n, ¬ G.Adj u v := by simpa only [not_exists] using hnone
  let D : Circuit := ⟨[], n⟩
  have hD : IsAO2 n D := by
    simp [D, IsAO2, PEqualNP.EdgeOwnership.AndOrOnly, NestedCover.ReadsBack]
  have hfun : circuitFun n D = NestedCover.graphFun G ∅ := by
    funext x
    simp [D, circuitFun, Circuit.eval, Circuit.wires, NestedCover.graphFun, hn]
  have hsize : C.size ≤ 0 := hC.2.2 D hD hfun
  have hjpos : 0 < (junk G C).card := Finset.card_pos.mpr hj
  exact (Nat.not_lt_zero _) (hjpos.trans_le ((junk_card_le_size G C).trans hsize))



namespace Normalization

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepW]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepW w g).length := by simp [stepW]; omega
    rw [ih (stepW w g) hlt]
    simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_char (gs : List Gate) (w : List Bool) :
    ∀ j, j < gs.length → (gs.foldl stepW w).getD (w.length + j) false =
      (gs.getD j ⟨GateOp.or, []⟩).op.eval ((gs.getD j ⟨GateOp.or, []⟩).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepW w).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen := foldl_len gs w
    simp only [List.length_append, List.length_singleton] at hj
    have key : ∀ i, i < w.length + gs.length →
        (stepW (gs.foldl stepW w) g).getD i false = (gs.foldl stepW w).getD i false := by
      intro i hi
      simp only [stepW, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_or_ge j gs.length with h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [e1, key _ (by omega), ih j h]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i (by omega)]
      · rfl
    · have hj' : j = gs.length := by omega
      subst hj'
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      have e2 : (stepW (gs.foldl stepW w) g).getD (w.length + gs.length) false =
          g.op.eval (g.inputs.map fun i => (gs.foldl stepW w).getD i false) := by
        simp only [stepW, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i hi]
      · simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by omega)]
        rfl

def wv (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

lemma wv_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    wv n C x w = x ⟨w, hw⟩ := by
  unfold wv
  rw [wires_eq, foldl_getD_lt _ _ _ (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

def AOB (n : ℕ) (C : Circuit) : Prop :=
  ∀ j, j < C.gates.length →
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
      ∀ i ∈ (gateAt C j).inputs, i < n + j

lemma wv_rec (n : ℕ) (C : Circuit) (x : Fin n → Bool) (hC : AOB n C) (j : ℕ)
    (hj : j < C.gates.length) :
    wv n C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (wv n C x)) := by
  have h := foldl_char C.gates (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  unfold wv gateAt
  rw [wires_eq, h]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [if_pos ((hC j hj).2 i hi)]

lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

lemma inCone_lt (n : ℕ) (C : Circuit) (i : ℕ) :
    ∀ j, InCone n C i j → i < j ∧ j < C.gates.length := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k, hk, _, h3 | h3⟩ := h
    · exact ⟨by omega, h0⟩
    · have := (ih k hk h3).1
      exact ⟨by omega, h0⟩

lemma inCone_reader (n : ℕ) (C : Circuit) (i : ℕ) :
    ∀ j, InCone n C i j → ∃ r, r < C.gates.length ∧ i < r ∧ n + i ∈ (gateAt C r).inputs ∧
      (r = j ∨ InCone n C r j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    have h' := h
    rw [inCone_iff] at h'
    obtain ⟨h0, k, hk, hin, h3 | h3⟩ := h'
    · subst h3
      exact ⟨j, h0, hk, hin, Or.inl rfl⟩
    · obtain ⟨r, hr, hir, hrin, h4⟩ := ih k hk h3
      refine ⟨r, hr, hir, hrin, Or.inr ?_⟩
      rw [inCone_iff]
      refine ⟨h0, k, hk, hin, ?_⟩
      rcases h4 with h4 | h4
      · exact Or.inl h4
      · exact Or.inr h4

def tau (n r b w : ℕ) : ℕ := if w < n + r then w else if w = n + r then b else w - 1

def rho (r k : ℕ) : ℕ := if k < r then k else k + 1

def IsRedirect (n : ℕ) (C C' : Circuit) (r b : ℕ) : Prop :=
  ∀ k, k < C.gates.length - 1 →
    gateAt C' k = ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩

lemma transfer (n : ℕ) (C C' : Circuit) (r b : ℕ) (x : Fin n → Bool) (R : Bool → Bool → Prop)
    (hRrefl : ∀ a, R a a) (hRtrans : ∀ a b c, R a b → R b c → R a c)
    (hRand : ∀ (l : List ℕ) (f f' : ℕ → Bool), (∀ w ∈ l, R (f w) (f' w)) →
      R (GateOp.and.eval (l.map f)) (GateOp.and.eval (l.map f')))
    (hRor : ∀ (l : List ℕ) (f f' : ℕ → Bool), (∀ w ∈ l, R (f w) (f' w)) →
      R (GateOp.or.eval (l.map f)) (GateOp.or.eval (l.map f')))
    (hC : AOB n C) (hC' : AOB n C') (hr : r < C.gates.length) (hb : b < n + r)
    (hlen : C.gates.length - 1 ≤ C'.gates.length)
    (hred : IsRedirect n C C' r b) :
    ∀ w, w < n + C.gates.length → (n + r ≤ w → R (wv n C x (n + r)) (wv n C x b)) →
      R (wv n C x w) (wv n C' x (tau n r b w)) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hR0
    by_cases h1 : w < n
    · have ht : tau n r b w = w := by unfold tau; rw [if_pos (by omega)]
      rw [ht, wv_input n C x w h1, wv_input n C' x w h1]
      exact hRrefl _
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      by_cases hk : k = r
      · subst hk
        have ht : tau n k b (n + k) = b := by unfold tau; simp
        have htb : tau n k b b = b := by unfold tau; rw [if_pos hb]
        have h2 := ih b (by omega) (by omega) (fun h => absurd h (by omega))
        rw [htb] at h2
        rw [ht]
        exact hRtrans _ _ _ (hR0 le_rfl) h2
      · have hkm : k < C.gates.length := by omega
        obtain ⟨k', hk'1, hk'2, hk'3⟩ : ∃ k', tau n r b (n + k) = n + k' ∧ rho r k' = k ∧
            k' < C.gates.length - 1 := by
          by_cases hkr : k < r
          · refine ⟨k, ?_, ?_, by omega⟩
            · unfold tau; rw [if_pos (by omega)]
            · unfold rho; rw [if_pos hkr]
          · refine ⟨k - 1, ?_, ?_, by omega⟩
            · unfold tau; rw [if_neg (by omega), if_neg (by omega)]; omega
            · unfold rho; rw [if_neg (by omega)]; omega
        have hg := hred k' hk'3
        rw [hk'2] at hg
        rw [hk'1, wv_rec n C x hC k hkm, wv_rec n C' x hC' k' (by omega), hg]
        simp only [List.map_map]
        have hin : ∀ w ∈ (gateAt C k).inputs,
            R (wv n C x w) ((wv n C' x ∘ tau n r b) w) := by
          intro w hw'
          have hlt := (hC k hkm).2 w hw'
          exact ih w hlt (by omega) (fun h => hR0 (by omega))
        rcases (hC k hkm).1 with hop | hop
        · rw [hop]; exact hRand _ _ _ hin
        · rw [hop]; exact hRor _ _ _ hin

lemma transfer_eq (n : ℕ) (C C' : Circuit) (r b : ℕ) (x : Fin n → Bool)
    (hC : AOB n C) (hC' : AOB n C') (hr : r < C.gates.length) (hb : b < n + r)
    (hlen : C.gates.length - 1 ≤ C'.gates.length)
    (hred : IsRedirect n C C' r b) :
    ∀ w, w < n + C.gates.length → (n + r ≤ w → wv n C x (n + r) = wv n C x b) →
      wv n C x w = wv n C' x (tau n r b w) := by
  refine transfer n C C' r b x (fun a b => a = b) (fun _ => rfl) (fun _ _ _ h1 h2 => h1.trans h2)
    ?_ ?_ hC hC' hr hb hlen hred
  · intro l f f' h
    rw [List.map_congr_left h]
  · intro l f f' h
    rw [List.map_congr_left h]

lemma transfer_le (n : ℕ) (C C' : Circuit) (r b : ℕ) (x : Fin n → Bool)
    (hC : AOB n C) (hC' : AOB n C') (hr : r < C.gates.length) (hb : b < n + r)
    (hlen : C.gates.length - 1 ≤ C'.gates.length)
    (hred : IsRedirect n C C' r b) :
    ∀ w, w < n + C.gates.length →
      (n + r ≤ w → (wv n C x (n + r) = true → wv n C x b = true)) →
      (wv n C x w = true → wv n C' x (tau n r b w) = true) := by
  refine transfer n C C' r b x (fun a b => a = true → b = true) (fun _ h => h)
    (fun _ _ _ h1 h2 h => h2 (h1 h)) ?_ ?_ hC hC' hr hb hlen hred
  · intro l f f' h hall
    simp only [GateOp.eval] at hall ⊢
    rw [List.all_eq_true] at hall ⊢
    intro v hv
    rw [List.mem_map] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact h w hw (hall (f w) (List.mem_map.mpr ⟨w, hw, rfl⟩))
  · intro l f f' h hany
    simp only [GateOp.eval] at hany ⊢
    rw [List.any_eq_true] at hany ⊢
    obtain ⟨v, hv, hv2⟩ := hany
    rw [List.mem_map] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact ⟨f' w, List.mem_map.mpr ⟨w, hw, rfl⟩, h w hw hv2⟩


def gfun (n : ℕ) (C : Circuit) (r b : ℕ) (top : Gate) (k : ℕ) : Gate :=
  if k < C.gates.length - 1 then
    ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩ else top

def V1 (n : ℕ) (C : Circuit) (r b : ℕ) : Circuit :=
  ⟨(List.range (C.gates.length - 1)).map (gfun n C r b ⟨GateOp.or, []⟩), tau n r b C.output⟩

def V2 (n : ℕ) (C : Circuit) (r b i : ℕ) : Circuit :=
  ⟨(List.range C.gates.length).map (gfun n C r b ⟨GateOp.or, [tau n r b C.output, n + i]⟩),
    n + C.gates.length - 1⟩

lemma gateAt_range (m : ℕ) (g : ℕ → Gate) (out k : ℕ) (hk : k < m) :
    gateAt ⟨(List.range m).map g, out⟩ k = g k := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma V1_len (n : ℕ) (C : Circuit) (r b : ℕ) :
    (V1 n C r b).gates.length = C.gates.length - 1 := by simp [V1]

lemma V2_len (n : ℕ) (C : Circuit) (r b i : ℕ) :
    (V2 n C r b i).gates.length = C.gates.length := by simp [V2]

lemma V1_gate (n : ℕ) (C : Circuit) (r b k : ℕ) (hk : k < C.gates.length - 1) :
    gateAt (V1 n C r b) k =
      ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩ := by
  unfold V1
  rw [gateAt_range _ _ _ _ hk]
  unfold gfun
  rw [if_pos hk]

lemma V2_gate (n : ℕ) (C : Circuit) (r b i k : ℕ) (hk : k < C.gates.length - 1) :
    gateAt (V2 n C r b i) k =
      ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩ := by
  unfold V2
  rw [gateAt_range _ _ _ _ (by omega)]
  unfold gfun
  rw [if_pos hk]

lemma V2_top (n : ℕ) (C : Circuit) (r b i : ℕ) (hm : 0 < C.gates.length) :
    gateAt (V2 n C r b i) (C.gates.length - 1) =
      ⟨GateOp.or, [tau n r b C.output, n + i]⟩ := by
  unfold V2
  rw [gateAt_range _ _ _ _ (by omega)]
  unfold gfun
  rw [if_neg (by omega)]

def AO2 (n : ℕ) (C : Circuit) : Prop :=
  ∀ j, j < C.gates.length →
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
      (∃ a b, (gateAt C j).inputs = [a, b]) ∧ ∀ i ∈ (gateAt C j).inputs, i < n + j

lemma aob {n : ℕ} {C : Circuit} (h : AO2 n C) : AOB n C :=
  fun j hj => ⟨(h j hj).1, (h j hj).2.2⟩

lemma rho_lt (r k m : ℕ) (hr : r < m) (hk : k < m - 1) : rho r k < m := by
  unfold rho; split_ifs <;> omega

lemma tau_lt (n r b w k : ℕ) (hb : b < n + r) (hw : w < n + rho r k) :
    tau n r b w < n + k := by
  unfold tau; unfold rho at hw; split_ifs at hw ⊢ <;> omega

lemma tau_low (n r b w : ℕ) (hw : w < n + r) : tau n r b w = w := by
  unfold tau; rw [if_pos hw]

lemma tau_rho (n r b k : ℕ) : tau n r b (n + rho r k) = n + k := by
  unfold tau rho; split_ifs <;> omega

lemma eval_or_pair (f : ℕ → Bool) (a b : ℕ) :
    GateOp.or.eval ([a, b].map f) = (f a || f b) := by simp [GateOp.eval]

lemma eval_and_pair (f : ℕ → Bool) (a b : ℕ) :
    GateOp.and.eval ([a, b].map f) = (f a && f b) := by simp [GateOp.eval]

lemma V1_AO2 (n : ℕ) (C : Circuit) (r b : ℕ) (hC : AO2 n C) (hr : r < C.gates.length)
    (hb : b < n + r) : AO2 n (V1 n C r b) := by
  intro k hk
  rw [V1_len] at hk
  rw [V1_gate n C r b k hk]
  obtain ⟨h1, ⟨a, c, h2⟩, h3⟩ := hC (rho r k) (rho_lt r k _ hr hk)
  refine ⟨h1, ⟨tau n r b a, tau n r b c, by simp [h2]⟩, ?_⟩
  intro w hw
  simp only [List.mem_map] at hw
  obtain ⟨w0, hw0, rfl⟩ := hw
  exact tau_lt n r b w0 k hb (h3 w0 hw0)

lemma V2_AO2 (n : ℕ) (C : Circuit) (r b i : ℕ) (hC : AO2 n C) (hr : r < C.gates.length)
    (hb : b < n + r) (hi : i < r) (hout : C.output < n + C.gates.length) :
    AO2 n (V2 n C r b i) := by
  intro k hk
  rw [V2_len] at hk
  by_cases hk1 : k < C.gates.length - 1
  · rw [V2_gate n C r b i k hk1]
    obtain ⟨h1, ⟨a, c, h2⟩, h3⟩ := hC (rho r k) (rho_lt r k _ hr hk1)
    refine ⟨h1, ⟨tau n r b a, tau n r b c, by simp [h2]⟩, ?_⟩
    intro w hw
    simp only [List.mem_map] at hw
    obtain ⟨w0, hw0, rfl⟩ := hw
    exact tau_lt n r b w0 k hb (h3 w0 hw0)
  · have hk2 : k = C.gates.length - 1 := by omega
    subst hk2
    rw [V2_top n C r b i (by omega)]
    refine ⟨Or.inr rfl, ⟨_, _, rfl⟩, ?_⟩
    intro w hw
    have hw' : w = tau n r b C.output ∨ w = n + i := by simpa using hw
    rcases hw' with rfl | rfl
    · unfold tau; split_ifs <;> omega
    · omega

lemma V1_red (n : ℕ) (C : Circuit) (r b : ℕ) : IsRedirect n C (V1 n C r b) r b :=
  fun k hk => V1_gate n C r b k hk

lemma V2_red (n : ℕ) (C : Circuit) (r b i : ℕ) : IsRedirect n C (V2 n C r b i) r b :=
  fun k hk => V2_gate n C r b i k hk

lemma V1_fun (n : ℕ) (C : Circuit) (r b : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hout : C.output < n + C.gates.length)
    (h1 : wv n C x b = true → wv n C x C.output = true)
    (h2 : wv n C x b = false → wv n C x (n + r) = false) :
    wv n (V1 n C r b) x (V1 n C r b).output = wv n C x C.output := by
  have hC' := V1_AO2 n C r b hC hr hb
  have hlen : C.gates.length - 1 ≤ (V1 n C r b).gates.length := by rw [V1_len]
  show wv n (V1 n C r b) x (tau n r b C.output) = wv n C x C.output
  cases hbv : wv n C x b with
  | true =>
    rw [h1 hbv]
    exact transfer_le n C _ r b x (aob hC) (aob hC') hr hb hlen (V1_red n C r b) C.output hout
      (fun _ _ => hbv) (h1 hbv)
  | false =>
    exact (transfer_eq n C _ r b x (aob hC) (aob hC') hr hb hlen (V1_red n C r b) C.output hout
      (fun _ => by rw [h2 hbv, hbv])).symm

lemma V2_low (n : ℕ) (C : Circuit) (r b i : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length) :
    ∀ w, w < n + r → wv n (V2 n C r b i) x w = wv n C x w := by
  intro w hw
  have h := transfer_eq n C _ r b x (aob hC) (aob (V2_AO2 n C r b i hC hr hb hi hout)) hr hb
    (by rw [V2_len]; omega) (V2_red n C r b i) w (by omega) (fun h => absurd h (by omega))
  rw [tau_low n r b w hw] at h
  exact h.symm

lemma V2_same (n : ℕ) (C : Circuit) (r b i : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length) (h0 : wv n C x (n + r) = wv n C x b) :
    ∀ w, w < n + C.gates.length → wv n (V2 n C r b i) x (tau n r b w) = wv n C x w := by
  intro w hw
  exact (transfer_eq n C _ r b x (aob hC) (aob (V2_AO2 n C r b i hC hr hb hi hout)) hr hb
    (by rw [V2_len]; omega) (V2_red n C r b i) w hw (fun _ => h0)).symm

lemma V2_out (n : ℕ) (C : Circuit) (r b i : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length)
    (hbel : wv n C x (n + i) = true → wv n C x C.output = true)
    (h0 : wv n C x (n + i) = false → wv n C x (n + r) = wv n C x b) :
    wv n (V2 n C r b i) x (V2 n C r b i).output = wv n C x C.output := by
  have hC' := V2_AO2 n C r b i hC hr hb hi hout
  have hm : 0 < C.gates.length := by omega
  have e : (V2 n C r b i).output = n + (C.gates.length - 1) := by
    show n + C.gates.length - 1 = _
    omega
  rw [e, wv_rec n _ x (aob hC') (C.gates.length - 1) (by rw [V2_len]; omega),
    V2_top n C r b i hm]
  have hi' := V2_low n C r b i x hC hr hb hi hout (n + i) (by omega)
  dsimp only
  rw [eval_or_pair, hi']
  cases hv : wv n C x (n + i) with
  | true => rw [hbel hv]; simp
  | false =>
    rw [V2_same n C r b i x hC hr hb hi hout (h0 hv) C.output hout]; simp

lemma V1_fun_top (n : ℕ) (D : Circuit) (r c i y : ℕ) (x : Fin n → Bool) (hD : AO2 n D)
    (hr : r < D.gates.length - 1) (hc : c < n + r) (hi : i < r)
    (hout : D.output = n + (D.gates.length - 1))
    (htop : gateAt D (D.gates.length - 1) = ⟨GateOp.or, [y, n + i]⟩)
    (h0 : wv n D x (n + i) = false → wv n D x (n + r) = wv n D x c) :
    wv n (V1 n D r c) x (V1 n D r c).output = wv n D x D.output := by
  have hr' : r < D.gates.length := by omega
  have hE := V1_AO2 n D r c hD hr' hc
  have hlen : D.gates.length - 1 ≤ (V1 n D r c).gates.length := by rw [V1_len]
  have hred := V1_red n D r c
  show wv n (V1 n D r c) x (tau n r c D.output) = wv n D x D.output
  cases hv : wv n D x (n + i) with
  | false =>
    exact (transfer_eq n D _ r c x (aob hD) (aob hE) hr' hc hlen hred D.output (by omega)
      (fun _ => h0 hv)).symm
  | true =>
    have e1 : wv n D x D.output = true := by
      rw [hout, wv_rec n D x (aob hD) _ (by omega), htop]
      dsimp only
      rw [eval_or_pair, hv]; simp
    have e2 : tau n r c D.output = n + (D.gates.length - 2) := by
      rw [hout]; unfold tau; rw [if_neg (by omega), if_neg (by omega)]; omega
    have e3 : gateAt (V1 n D r c) (D.gates.length - 2) =
        ⟨GateOp.or, [tau n r c y, n + i]⟩ := by
      rw [V1_gate n D r c _ (by omega)]
      have hrho : rho r (D.gates.length - 2) = D.gates.length - 1 := by
        unfold rho; rw [if_neg (by omega)]; omega
      rw [hrho, htop]
      simp [tau_low n r c (n + i) (by omega)]
    have e4 : wv n (V1 n D r c) x (n + i) = true := by
      have h := transfer_eq n D _ r c x (aob hD) (aob hE) hr' hc hlen hred (n + i) (by omega)
        (fun h => absurd h (by omega))
      rw [tau_low n r c (n + i) (by omega)] at h
      rw [← h, hv]
    rw [e1, e2, wv_rec n _ x (aob hE) _ (by rw [V1_len]; omega), e3]
    dsimp only
    rw [eval_or_pair, e4]; simp

def Least (n : ℕ) (C : Circuit) : Prop :=
  AO2 n C ∧ ∀ D : Circuit, AO2 n D → (∀ x, wv n D x D.output = wv n C x C.output) →
    C.gates.length ≤ D.gates.length

lemma reader_or (n : ℕ) (C : Circuit) (hL : Least n C) (hout : C.output < n + C.gates.length)
    (i r : ℕ) (hr : r < C.gates.length)
    (hbel : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true)
    (hin : n + i ∈ (gateAt C r).inputs) :
    (gateAt C r).op = GateOp.or ∧ ∃ c, c ≠ n + i ∧ c < n + r ∧
      ((gateAt C r).inputs = [n + i, c] ∨ (gateAt C r).inputs = [c, n + i]) := by
  obtain ⟨hop, ⟨a, c0, hab⟩, hlt⟩ := hL.1 r hr
  have hir : n + i < n + r := hlt _ hin
  have hin' : n + i = a ∨ n + i = c0 := by rw [hab] at hin; simpa using hin
  by_contra hcon
  have key : ∀ x, wv n C x (n + i) = false → wv n C x (n + r) = false := by
    intro x hx
    rw [wv_rec n C x (aob hL.1) r hr, hab]
    rcases hop with hop | hop
    · rw [hop, eval_and_pair]
      rcases hin' with h | h
      · rw [← h, hx]; rfl
      · rw [← h, hx]; simp
    · rw [hop, eval_or_pair]
      have ha : a = n + i := by
        by_contra hne
        apply hcon
        refine ⟨hop, a, hne, hlt a (by rw [hab]; simp), ?_⟩
        rcases hin' with h | h
        · exact absurd h.symm hne
        · right; rw [hab, h]
      have hc : c0 = n + i := by
        by_contra hne
        apply hcon
        refine ⟨hop, c0, hne, hlt c0 (by rw [hab]; simp), ?_⟩
        left; rw [hab, ha]
      rw [ha, hc, hx]; rfl
  have hfun : ∀ x, wv n (V1 n C r (n + i)) x (V1 n C r (n + i)).output = wv n C x C.output :=
    fun x => V1_fun n C r (n + i) x hL.1 hr hir hout (hbel x) (key x)
  have hle := hL.2 _ (V1_AO2 n C r (n + i) hL.1 hr hir) hfun
  rw [V1_len] at hle
  omega

lemma reader_unique (n : ℕ) (C : Circuit) (hL : Least n C)
    (hout : C.output < n + C.gates.length) (i r1 r2 : ℕ) (h12 : r1 < r2)
    (hr2 : r2 < C.gates.length)
    (hbel : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true)
    (hin1 : n + i ∈ (gateAt C r1).inputs) (hin2 : n + i ∈ (gateAt C r2).inputs) : False := by
  have hr1 : r1 < C.gates.length := by omega
  obtain ⟨hop1, c1, hc1, hc1lt, hi1⟩ := reader_or n C hL hout i r1 hr1 hbel hin1
  obtain ⟨hop2, c2, hc2, hc2lt, hi2⟩ := reader_or n C hL hout i r2 hr2 hbel hin2
  have hir1 : i < r1 := by have := (hL.1 r1 hr1).2.2 _ hin1; omega
  have hir2 : i < r2 := by omega
  have k2 : ∀ x, wv n C x (n + i) = false → wv n C x (n + r2) = wv n C x c2 := by
    intro x hx
    rw [wv_rec n C x (aob hL.1) r2 hr2, hop2]
    rcases hi2 with h | h
    · rw [h, eval_or_pair, hx]; rfl
    · rw [h, eval_or_pair, hx]; simp
  have k1 : ∀ x, wv n C x (n + i) = false → wv n C x (n + r1) = wv n C x c1 := by
    intro x hx
    rw [wv_rec n C x (aob hL.1) r1 hr1, hop1]
    rcases hi1 with h | h
    · rw [h, eval_or_pair, hx]; rfl
    · rw [h, eval_or_pair, hx]; simp
  have hD : AO2 n (V2 n C r2 c2 i) := V2_AO2 n C r2 c2 i hL.1 hr2 hc2lt hir2 hout
  have hDlen := V2_len n C r2 c2 i
  have hDfun : ∀ x, wv n (V2 n C r2 c2 i) x (V2 n C r2 c2 i).output = wv n C x C.output :=
    fun x => V2_out n C r2 c2 i x hL.1 hr2 hc2lt hir2 hout (hbel x) (k2 x)
  have hDout : (V2 n C r2 c2 i).output = n + ((V2 n C r2 c2 i).gates.length - 1) := by
    rw [hDlen]
    show n + C.gates.length - 1 = n + (C.gates.length - 1)
    omega
  have hDtop : gateAt (V2 n C r2 c2 i) ((V2 n C r2 c2 i).gates.length - 1) =
      ⟨GateOp.or, [tau n r2 c2 C.output, n + i]⟩ := by
    rw [hDlen]
    exact V2_top n C r2 c2 i (by omega)
  have h0 : ∀ x, wv n (V2 n C r2 c2 i) x (n + i) = false →
      wv n (V2 n C r2 c2 i) x (n + r1) = wv n (V2 n C r2 c2 i) x c1 := by
    intro x hx
    rw [V2_low n C r2 c2 i x hL.1 hr2 hc2lt hir2 hout (n + i) (by omega)] at hx
    rw [V2_low n C r2 c2 i x hL.1 hr2 hc2lt hir2 hout (n + r1) (by omega),
      V2_low n C r2 c2 i x hL.1 hr2 hc2lt hir2 hout c1 (by omega)]
    exact k1 x hx
  have hEfun : ∀ x, wv n (V1 n (V2 n C r2 c2 i) r1 c1) x (V1 n (V2 n C r2 c2 i) r1 c1).output =
      wv n C x C.output := fun x =>
    (V1_fun_top n (V2 n C r2 c2 i) r1 c1 i (tau n r2 c2 C.output) x hD (by rw [hDlen]; omega)
      hc1lt hir1 hDout hDtop (h0 x)).trans (hDfun x)
  have hle := hL.2 _ (V1_AO2 n (V2 n C r2 c2 i) r1 c1 hD (by rw [hDlen]; omega) hc1lt) hEfun
  rw [V1_len, hDlen] at hle
  omega

lemma inCone_trans (n : ℕ) (C : Circuit) (a k : ℕ) (hak : InCone n C a k) :
    ∀ j, InCone n C k j → InCone n C a j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k2, hk2, hin, h3 | h3⟩ := h
    · subst h3
      rw [inCone_iff]
      exact ⟨h0, k, hk2, hin, Or.inr hak⟩
    · rw [inCone_iff]
      exact ⟨h0, k2, hk2, hin, Or.inr (ih k2 hk2 h3)⟩

lemma V2_cone (n : ℕ) (C : Circuit) (r c i : ℕ) (hC : AO2 n C) (hr : r < C.gates.length)
    (hc : c < n + r) (hcin : c ∈ (gateAt C r).inputs) (a' : ℕ) :
    ∀ b', b' < C.gates.length - 1 → InCone n (V2 n C r c i) a' b' →
      InCone n C (rho r a') (rho r b') := by
  intro b'
  induction b' using Nat.strong_induction_on with
  | _ b' ih =>
    intro hb' h
    rw [inCone_iff] at h
    obtain ⟨_, k', hk', hin, h3⟩ := h
    rw [V2_gate n C r c i b' hb'] at hin
    simp only [List.mem_map] at hin
    obtain ⟨w, hw, hwk⟩ := hin
    have hbm : rho r b' < C.gates.length := rho_lt r b' _ hr hb'
    have hwlt := (hC (rho r b') hbm).2.2 w hw
    have hrb : rho r b' ≤ b' + 1 := by unfold rho; split_ifs <;> omega
    have hrb2 : b' < r → rho r b' = b' := by intro h; unfold rho; rw [if_pos h]
    have hstep : InCone n C (rho r k') (rho r b') := by
      unfold tau at hwk
      by_cases h1 : w < n + r
      · rw [if_pos h1] at hwk
        have e : rho r k' = k' := by unfold rho; rw [if_pos (by omega)]
        rw [e, inCone_iff]
        refine ⟨hbm, k', by omega, ?_, Or.inl rfl⟩
        rw [← hwk]; exact hw
      · rw [if_neg h1] at hwk
        by_cases h2 : w = n + r
        · rw [if_pos h2] at hwk
          have e : rho r k' = k' := by unfold rho; rw [if_pos (by omega)]
          rw [e]
          have s1 : InCone n C k' r := by
            rw [inCone_iff]
            refine ⟨hr, k', by omega, ?_, Or.inl rfl⟩
            rw [← hwk]; exact hcin
          have s2 : InCone n C r (rho r b') := by
            rw [inCone_iff]
            refine ⟨hbm, r, by omega, ?_, Or.inl rfl⟩
            rw [← h2]; exact hw
          exact inCone_trans n C k' r s1 _ s2
        · rw [if_neg h2] at hwk
          have e : rho r k' = k' + 1 := by unfold rho; rw [if_neg (by omega)]
          rw [e, inCone_iff]
          refine ⟨hbm, k' + 1, by omega, ?_, Or.inl rfl⟩
          have e2 : n + (k' + 1) = w := by omega
          rw [e2]; exact hw
    rcases h3 with h3 | h3
    · rw [h3]; exact hstep
    · exact inCone_trans n C _ _ (ih k' hk' (by omega) h3) _ hstep

lemma V2_no_reader (n : ℕ) (C : Circuit) (r c i : ℕ) (hr : r < C.gates.length)
    (hi : i < r) (hci : c ≠ n + i)
    (huniq : ∀ k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → k = r) :
    ∀ k', k' < C.gates.length - 1 → n + i ∉ (gateAt (V2 n C r c i) k').inputs := by
  intro k' hk' hin
  rw [V2_gate n C r c i k' hk'] at hin
  simp only [List.mem_map] at hin
  obtain ⟨w, hw, hwk⟩ := hin
  have hbm : rho r k' < C.gates.length := rho_lt r k' _ hr hk'
  have hne : rho r k' ≠ r := by unfold rho; split_ifs <;> omega
  unfold tau at hwk
  by_cases h1 : w < n + r
  · rw [if_pos h1] at hwk
    rw [hwk] at hw
    exact hne (huniq _ hbm hw)
  · rw [if_neg h1] at hwk
    by_cases h2 : w = n + r
    · rw [if_pos h2] at hwk
      exact hci hwk
    · rw [if_neg h2] at hwk
      omega

lemma V2_no_cone (n : ℕ) (C : Circuit) (r c i : ℕ) (hr : r < C.gates.length)
    (hi : i < r) (hci : c ≠ n + i)
    (huniq : ∀ k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → k = r) :
    ∀ j', j' < C.gates.length - 1 → ¬ InCone n (V2 n C r c i) i j' := by
  intro j' hj' h
  obtain ⟨r', _, _, hrin, h4⟩ := inCone_reader n _ i j' h
  have hr'j : r' ≤ j' := by
    rcases h4 with h4 | h4
    · omega
    · have := (inCone_lt n _ r' j' h4).1
      omega
  exact V2_no_reader n C r c i hr hi hci huniq r' (by omega) hrin


lemma rho_inj (r : ℕ) : Function.Injective (rho r) := by
  intro a b h
  unfold rho at h
  split_ifs at h <;> omega

lemma rho_ne (r k : ℕ) : rho r k ≠ r := by
  unfold rho; split_ifs <;> omega

lemma rho_surj (r k m : ℕ) (hr : r < m) (hk : k < m) (hne : k ≠ r) : ∃ k', k' < m - 1 ∧ rho r k' = k := by
  by_cases h : k < r
  · exact ⟨k, by omega, by unfold rho; rw [if_pos h]⟩
  · exact ⟨k - 1, by omega, by unfold rho; rw [if_neg (by omega)]; omega⟩

lemma wires_len (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq, foldl_len, List.length_ofFn]

lemma out_lt (n : ℕ) (C : Circuit) (x : Fin n → Bool) (h : wv n C x C.output = true) :
    C.output < n + C.gates.length := by
  by_contra hge
  unfold wv at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [wires_len]; omega)] at h
  simp at h

lemma step3_core (n : ℕ) (C : Circuit) (hL : Least n C) (hout : C.output < n + C.gates.length)
    (i j : ℕ) (hbel : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true)
    (hcone : InCone n C i j) :
    ∃ r c, r < C.gates.length ∧ i < r ∧ c < n + r ∧ c ≠ n + i ∧ c ∈ (gateAt C r).inputs ∧
      (gateAt C r).op = GateOp.or ∧
      (∀ k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → k = r) ∧
      (∀ x, wv n C x (n + i) = false → wv n C x (n + r) = wv n C x c) := by
  obtain ⟨r, hr, hir, hrin, _⟩ := inCone_reader n C i j hcone
  obtain ⟨hop, c, hc, hclt, hi⟩ := reader_or n C hL hout i r hr hbel hrin
  refine ⟨r, c, hr, hir, hclt, hc, ?_, hop, ?_, ?_⟩
  · rcases hi with h | h <;> rw [h] <;> simp
  · intro k hk hkin
    rcases Nat.lt_trichotomy k r with h | h | h
    · exact (reader_unique n C hL hout i k r h hr hbel hkin hrin).elim
    · exact h
    · exact (reader_unique n C hL hout i r k h hk hbel hrin hkin).elim
  · intro x hx
    rw [wv_rec n C x (aob hL.1) r hr, hop]
    rcases hi with h | h
    · rw [h, eval_or_pair, hx]; rfl
    · rw [h, eval_or_pair, hx]; simp

lemma least_of_same (n : ℕ) (C D : Circuit) (hL : Least n C) (hD : AO2 n D)
    (hfun : ∀ x, wv n D x D.output = wv n C x C.output)
    (hlen : D.gates.length = C.gates.length) : Least n D :=
  ⟨hD, fun E hE hEf => by rw [hlen]; exact hL.2 E hE (fun x => (hEf x).trans (hfun x))⟩

lemma V2_gateval (n : ℕ) (C : Circuit) (r c i : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : c < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length) (h0 : wv n C x (n + r) = wv n C x c)
    (k' : ℕ) (hk' : k' < C.gates.length - 1) :
    wv n (V2 n C r c i) x (n + k') = wv n C x (n + rho r k') := by
  have h := V2_same n C r c i x hC hr hb hi hout h0 (n + rho r k')
    (by have := rho_lt r k' _ hr hk'; omega)
  rw [tau_rho] at h
  exact h

lemma V2_below (n : ℕ) (C : Circuit) (r c i : ℕ) (F : (Fin n → Bool) → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : c < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length)
    (hbelF : ∀ x, wv n C x (n + i) = true → F x = true)
    (h0 : ∀ x, wv n C x (n + i) = false → wv n C x (n + r) = wv n C x c)
    (k' : ℕ) (hk' : k' < C.gates.length - 1) :
    (∀ x, wv n (V2 n C r c i) x (n + k') = true → F x = true) ↔
      (∀ x, wv n C x (n + rho r k') = true → F x = true) := by
  constructor
  · intro h x hv
    cases hx : wv n C x (n + i) with
    | true => exact hbelF x hx
    | false =>
      apply h x
      rw [V2_gateval n C r c i x hC hr hb hi hout (h0 x hx) k' hk']
      exact hv
  · intro h x hv
    cases hx : wv n C x (n + i) with
    | true => exact hbelF x hx
    | false =>
      apply h x
      rw [← V2_gateval n C r c i x hC hr hb hi hout (h0 x hx) k' hk']
      exact hv


lemma card_filter_rho (m r : ℕ) (hr : r < m) (P Q : ℕ → Prop) [DecidablePred P]
    [DecidablePred Q]
    (hPQ : ∀ k', k' < m - 1 → (Q k' ↔ P (rho r k'))) (hPr : ¬ P r) (hQ : ¬ Q (m - 1)) :
    ((Finset.range m).filter Q).card = ((Finset.range m).filter P).card := by
  apply Finset.card_bij (fun k' _ => rho r k')
  · intro k' hk'
    rw [Finset.mem_filter, Finset.mem_range] at hk' ⊢
    have hlt : k' < m - 1 := by
      rcases Nat.lt_or_ge k' (m - 1) with h | h
      · exact h
      · have hk'' : k' = m - 1 := by omega
        rw [hk''] at hk'
        exact absurd hk'.2 hQ
    exact ⟨rho_lt r k' m hr hlt, (hPQ k' hlt).mp hk'.2⟩
  · intro a _ b _ h
    exact rho_inj r h
  · intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk
    have hne : k ≠ r := fun h => hPr (h ▸ hk.2)
    obtain ⟨k', hk'1, hk'2⟩ := rho_surj r k m hr hk.1 hne
    refine ⟨k', ?_, hk'2⟩
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, (hPQ k' hk'1).mpr (hk'2 ▸ hk.2)⟩

lemma card_pairs_rho (m r : ℕ) (hr : r < m) (P Q : ℕ → ℕ → Prop)
    [DecidablePred (fun p : ℕ × ℕ => P p.1 p.2)] [DecidablePred (fun p : ℕ × ℕ => Q p.1 p.2)]
    (hQP : ∀ a' b', a' < m → b' < m → Q a' b' →
      a' < m - 1 ∧ b' < m - 1 ∧ P (rho r a') (rho r b'))
    (i j : ℕ) (hi : i < m) (hj : j < m) (hP : P i j)
    (hne : ∀ a' b', Q a' b' → ¬ (rho r a' = i ∧ rho r b' = j)) :
    ((Finset.range m ×ˢ Finset.range m).filter (fun p : ℕ × ℕ => Q p.1 p.2)).card <
      ((Finset.range m ×ˢ Finset.range m).filter (fun p : ℕ × ℕ => P p.1 p.2)).card := by
  have hinj : Function.Injective (fun p : ℕ × ℕ => (rho r p.1, rho r p.2)) := by
    intro p q h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (rho_inj r h.1) (rho_inj r h.2)
  rw [← Finset.card_image_of_injective _ hinj]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨(i, j), ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
      exact ⟨⟨hi, hj⟩, hP⟩
    · intro hmem
      rw [Finset.mem_image] at hmem
      obtain ⟨⟨a', b'⟩, hab, heq⟩ := hmem
      rw [Finset.mem_filter] at hab
      simp only [Prod.mk.injEq] at heq
      exact hne a' b' hab.2 heq
  · intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨⟨a', b'⟩, hab, rfl⟩ := hp
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hab
    obtain ⟨h1, h2, h3⟩ := hQP a' b' hab.1.1 hab.1.2 hab.2
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact ⟨⟨rho_lt r a' m hr h1, rho_lt r b' m hr h2⟩, h3⟩


lemma step3_struct (n : ℕ) (C : Circuit) (F : (Fin n → Bool) → Bool) (hL : Least n C)
    (hF : ∀ x, wv n C x C.output = F x) (hout : C.output < n + C.gates.length)
    (i j : ℕ) (hbel : ∀ x, wv n C x (n + i) = true → F x = true)
    (hcone : InCone n C i j) :
    ∃ (C' : Circuit) (r : ℕ), r < C.gates.length ∧ i < r ∧ Least n C' ∧
      (∀ x, wv n C' x C'.output = F x) ∧ C'.gates.length = C.gates.length ∧
      (∀ k', k' < C.gates.length - 1 → (gateAt C' k').op = (gateAt C (rho r k')).op) ∧
      (gateAt C' (C.gates.length - 1)).op = GateOp.or ∧ (gateAt C r).op = GateOp.or ∧
      (∀ k', k' < C.gates.length - 1 →
        ((∀ x, wv n C' x (n + k') = true → F x = true) ↔
          (∀ x, wv n C x (n + rho r k') = true → F x = true))) ∧
      (∀ a' b', b' < C.gates.length - 1 → InCone n C' a' b' →
        InCone n C (rho r a') (rho r b')) ∧
      (∀ j', j' < C.gates.length - 1 → ¬ InCone n C' i j') := by
  have hbel' : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true :=
    fun x h => by rw [hF]; exact hbel x h
  obtain ⟨r, c, hr, hir, hclt, hci, hcin, hop, huniq, h0⟩ :=
    step3_core n C hL hout i j hbel' hcone
  have hD := V2_AO2 n C r c i hL.1 hr hclt hir hout
  have hfun : ∀ x, wv n (V2 n C r c i) x (V2 n C r c i).output = wv n C x C.output :=
    fun x => V2_out n C r c i x hL.1 hr hclt hir hout (hbel' x) (h0 x)
  refine ⟨V2 n C r c i, r, hr, hir, least_of_same n C _ hL hD hfun (V2_len n C r c i),
    fun x => (hfun x).trans (hF x), V2_len n C r c i, ?_, ?_, hop, ?_, ?_, ?_⟩
  · intro k' hk'
    rw [V2_gate n C r c i k' hk']
  · rw [V2_top n C r c i (by omega)]
  · intro k' hk'
    exact V2_below n C r c i F hL.1 hr hclt hir hout hbel h0 k' hk'
  · intro a' b' hb' h
    exact V2_cone n C r c i hL.1 hr hclt hcin a' b' hb' h
  · exact V2_no_cone n C r c i hr hir hci huniq

lemma pairs_lt (n : ℕ) (C C' : Circuit) (r i j : ℕ) (hr : r < C.gates.length) (hir : i < r)
    (hlen : C'.gates.length = C.gates.length)
    (hops : ∀ k', k' < C.gates.length - 1 → (gateAt C' k').op = (gateAt C (rho r k')).op)
    (htop : (gateAt C' (C.gates.length - 1)).op = GateOp.or)
    (hcone : ∀ a' b', b' < C.gates.length - 1 → InCone n C' a' b' →
        InCone n C (rho r a') (rho r b'))
    (hno : ∀ j', j' < C.gates.length - 1 → ¬ InCone n C' i j')
    (hi : (gateAt C i).op = GateOp.and) (hj : (gateAt C j).op = GateOp.and)
    (hij : InCone n C i j)
    [DecidablePred (fun p : ℕ × ℕ => (gateAt C p.1).op = GateOp.and ∧
      (gateAt C p.2).op = GateOp.and ∧ InCone n C p.1 p.2)]
    [DecidablePred (fun p : ℕ × ℕ => (gateAt C' p.1).op = GateOp.and ∧
      (gateAt C' p.2).op = GateOp.and ∧ InCone n C' p.1 p.2)] :
    ((Finset.range C'.gates.length ×ˢ Finset.range C'.gates.length).filter
      (fun p : ℕ × ℕ => (gateAt C' p.1).op = GateOp.and ∧
        (gateAt C' p.2).op = GateOp.and ∧ InCone n C' p.1 p.2)).card <
    ((Finset.range C.gates.length ×ˢ Finset.range C.gates.length).filter
      (fun p : ℕ × ℕ => (gateAt C p.1).op = GateOp.and ∧
        (gateAt C p.2).op = GateOp.and ∧ InCone n C p.1 p.2)).card := by
  rw [hlen]
  have hjm := (inCone_lt n C i j hij)
  refine card_pairs_rho C.gates.length r hr
    (fun a b => (gateAt C a).op = GateOp.and ∧ (gateAt C b).op = GateOp.and ∧ InCone n C a b)
    (fun a b => (gateAt C' a).op = GateOp.and ∧ (gateAt C' b).op = GateOp.and ∧
      InCone n C' a b) ?_ i j (by omega) hjm.2 ⟨hi, hj, hij⟩ ?_
  · rintro a' b' _ hb' ⟨ha, hb, hab⟩
    have hb'' : b' < C.gates.length - 1 := by
      rcases Nat.lt_or_ge b' (C.gates.length - 1) with h | h
      · exact h
      · have e : b' = C.gates.length - 1 := by omega
        rw [e, htop] at hb
        exact absurd hb (by simp)
    have ha' := (inCone_lt n C' a' b' hab).1
    have ha'' : a' < C.gates.length - 1 := by omega
    refine ⟨ha'', hb'', ?_, ?_, hcone a' b' hb'' hab⟩
    · rw [← hops a' ha'']; exact ha
    · rw [← hops b' hb'']; exact hb
  · rintro a' b' ⟨_, hb, hab⟩ ⟨h1, _⟩
    have hb'' : b' < C.gates.length - 1 := by
      rcases Nat.lt_or_ge b' (C.gates.length - 1) with h | h
      · exact h
      · have hb3 := (inCone_lt n C' a' b' hab).2
        have e : b' = C.gates.length - 1 := by omega
        rw [e, htop] at hb
        exact absurd hb (by simp)
    have e : rho r i = i := by unfold rho; rw [if_pos hir]
    have e2 : a' = i := rho_inj r (h1.trans e.symm)
    rw [e2] at hab
    exact hno b' hb'' hab

lemma card_mem_rho (m r : ℕ) (hr : r < m) (P Q : ℕ → Prop) (S S' : Finset ℕ)
    (hS : ∀ k, k ∈ S ↔ k < m ∧ P k) (hS' : ∀ k, k ∈ S' ↔ k < m ∧ Q k)
    (hPQ : ∀ k', k' < m - 1 → (Q k' ↔ P (rho r k'))) (hPr : ¬ P r) (hQ : ¬ Q (m - 1)) :
    S'.card = S.card := by
  apply Finset.card_bij (fun k' _ => rho r k')
  · intro k' hk'
    rw [hS'] at hk'
    rw [hS]
    have hlt : k' < m - 1 := by
      rcases Nat.lt_or_ge k' (m - 1) with h | h
      · exact h
      · have hk'' : k' = m - 1 := by omega
        rw [hk''] at hk'
        exact absurd hk'.2 hQ
    exact ⟨rho_lt r k' m hr hlt, (hPQ k' hlt).mp hk'.2⟩
  · intro a _ b _ h
    exact rho_inj r h
  · intro k hk
    rw [hS] at hk
    have hne : k ≠ r := fun h => hPr (h ▸ hk.2)
    obtain ⟨k', hk'1, hk'2⟩ := rho_surj r k m hr hk.1 hne
    refine ⟨k', ?_, hk'2⟩
    rw [hS']
    exact ⟨by omega, (hPQ k' hk'1).mpr (hk'2 ▸ hk.2)⟩

lemma junk_eq (n : ℕ) (C C' : Circuit) (F : (Fin n → Bool) → Bool) (r : ℕ)
    (hr : r < C.gates.length)
    (hlen : C'.gates.length = C.gates.length)
    (hops : ∀ k', k' < C.gates.length - 1 → (gateAt C' k').op = (gateAt C (rho r k')).op)
    (htop : (gateAt C' (C.gates.length - 1)).op = GateOp.or)
    (hopr : (gateAt C r).op = GateOp.or)
    (hbelow : ∀ k', k' < C.gates.length - 1 →
        ((∀ x, wv n C' x (n + k') = true → F x = true) ↔
          (∀ x, wv n C x (n + rho r k') = true → F x = true)))
    (S S' : Finset ℕ)
    (hS : ∀ k, k ∈ S ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧
      ¬ ∀ x, wv n C x (n + k) = true → F x = true)
    (hS' : ∀ k, k ∈ S' ↔ k < C'.gates.length ∧ (gateAt C' k).op = GateOp.and ∧
      ¬ ∀ x, wv n C' x (n + k) = true → F x = true) :
    S'.card = S.card := by
  rw [hlen] at hS'
  apply card_mem_rho C.gates.length r hr _ _ S S' hS hS'
  · intro k' hk'
    rw [hops k' hk', hbelow k' hk']
  · rintro ⟨h, _⟩
    rw [hopr] at h
    exact absurd h (by simp)
  · rintro ⟨h, _⟩
    rw [htop] at h
    exact absurd h (by simp)


lemma gateAt_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  unfold gateAt
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

lemma mem_gateAt (C : Circuit) (g : Gate) (hg : g ∈ C.gates) :
    ∃ j, j < C.gates.length ∧ gateAt C j = g := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
  exact ⟨j, hj, by unfold gateAt; rw [List.getD_eq_getElem _ _ hj]⟩


lemma ao2_of (n : ℕ) (C : Circuit) (h : PEqualNP.TopForm.IsAO2 n C) : AO2 n C := by
  obtain ⟨h1, h2, h3⟩ := h
  intro j hj
  have hm := gateAt_mem C j hj
  exact ⟨h1 _ hm, List.length_eq_two.mp (h3 _ hm), h2 j hj⟩

lemma ao2_to (n : ℕ) (C : Circuit) (h : AO2 n C) : PEqualNP.TopForm.IsAO2 n C := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := mem_gateAt C g hg
    exact (h j hj).1
  · intro j hj
    exact (h j hj).2.2
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := mem_gateAt C g hg
    obtain ⟨a, b, hab⟩ := (h j hj).2.1
    rw [hab]
    rfl

lemma least_glue (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : PEqualNP.TopForm.IsLeastAO G C) :
    Least n C ∧ ∀ x, wv n C x C.output = graphFun G ∅ x := by
  obtain ⟨h1, h2, h3⟩ := hL
  have hF : ∀ x, wv n C x C.output = graphFun G ∅ x := fun x => congrFun h2 x
  refine ⟨⟨ao2_of n C h1, ?_⟩, hF⟩
  intro D hD hDf
  exact h3 D (ao2_to n D hD) (funext fun x => (hDf x).trans (hF x))

lemma least_glue' (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : Least n C) (hF : ∀ x, wv n C x C.output = graphFun G ∅ x) :
    PEqualNP.TopForm.IsLeastAO G C := by
  refine ⟨ao2_to n C hL.1, funext hF, ?_⟩
  intro D hD hDf
  exact hL.2 D (ao2_of n D hD) (fun x => (congrFun hDf x).trans (hF x).symm)

lemma exists_true (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : G.edgeFinset.Nonempty) : ∃ x : Fin n → Bool, graphFun G ∅ x = true := by
  refine ⟨fun _ => true, ?_⟩
  obtain ⟨e, he⟩ := hG
  rw [SimpleGraph.mem_edgeFinset] at he
  revert he
  refine Sym2.inductionOn e ?_
  intro u v he
  have hadj : G.Adj u v := he
  unfold graphFun
  have hd : decide (∃ u v, G.Adj u v ∧ (fun _ : Fin n => true) u = true ∧
      (fun _ : Fin n => true) v = true) = true := decide_eq_true ⟨u, v, hadj, rfl, rfl⟩
  rw [hd]
  simp

lemma mem_junk (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (k : ℕ) :
    k ∈ PEqualNP.TopForm.junk G C ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧
      ¬ ∀ x, wv n C x (n + k) = true → graphFun G ∅ x = true := by
  unfold PEqualNP.TopForm.junk PEqualNP.TopForm.gatesWhere
  rw [Finset.mem_filter, Finset.mem_range]
  unfold PEqualNP.CleanedNonEdge.IsDirtyAnd PEqualNP.CleanedNonEdge.IsDirty
  constructor
  · rintro ⟨h1, h2, _, x, hx1, hx2⟩
    refine ⟨h1, h2, fun h => ?_⟩
    have h3 := h x hx1
    rw [hx2] at h3
    exact absurd h3 (by simp)
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, h1, ?_⟩
    by_contra hne
    apply h3
    intro x hx
    by_contra hF
    exact hne ⟨x, hx, by simpa using hF⟩

open Classical in
lemma main_ind (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : G.edgeFinset.Nonempty) :
    ∀ k : ℕ, ∀ C : Circuit, PEqualNP.TopForm.IsLeastAO G C →
      ((Finset.range C.gates.length ×ˢ Finset.range C.gates.length).filter
        (fun p : ℕ × ℕ => (gateAt C p.1).op = GateOp.and ∧
          (gateAt C p.2).op = GateOp.and ∧ InCone n C p.1 p.2)).card = k →
      ∃ C' : Circuit, PEqualNP.TopForm.IsLeastAO G C' ∧ C'.size = C.size ∧
        (PEqualNP.TopForm.junk G C').card = (PEqualNP.TopForm.junk G C).card ∧
        PEqualNP.TopForm.TopForm G C' := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro C hC hk
    by_cases htop : PEqualNP.TopForm.TopForm G C
    · exact ⟨C, hC, rfl, rfl, htop⟩
    · have hex : ∃ i j, i < C.gates.length ∧ j < C.gates.length ∧
          (gateAt C i).op = GateOp.and ∧ PEqualNP.TopForm.BelowF G C i ∧
          (gateAt C j).op = GateOp.and ∧ InCone n C i j := by
        by_contra hne
        apply htop
        intro i hi j hj h1 h2 h3 h4
        exact hne ⟨i, j, hi, hj, h1, h2, h3, h4⟩
      obtain ⟨i, j, hi, hj, hopi, hbi, hopj, hcone⟩ := hex
      obtain ⟨hL, hF⟩ := least_glue n G C hC
      obtain ⟨x1, hx1⟩ := exists_true n G hG
      have hout : C.output < n + C.gates.length := out_lt n C x1 (by rw [hF]; exact hx1)
      obtain ⟨C', r, hr, hir, hL', hF', hlen, hops, htop', hopr, hbelow, hcn, hno⟩ :=
        step3_struct n C (graphFun G ∅) hL hF hout i j hbi hcone
      have hlt := pairs_lt n C C' r i j hr hir hlen hops htop' hcn hno hopi hopj hcone
      rw [hk] at hlt
      obtain ⟨C'', h1, h2, h3, h4⟩ := ih _ hlt C' (least_glue' n G C' hL' hF') rfl
      refine ⟨C'', h1, h2.trans hlen, h3.trans ?_, h4⟩
      refine junk_eq n C C' (graphFun G ∅) r hr hlen hops htop' hopr hbelow _ _ ?_ ?_
      · intro k
        exact mem_junk n G C k
      · intro k
        exact mem_junk n G C' k

end Normalization


namespace NormalizationBridge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadTwo

lemma foldl_wires_getD_lt (gs : List Gate) (acc : List Bool) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) acc).getD i false =
      acc.getD i false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]).length := by
      simp only [List.length_append, List.length_singleton]; omega
    rw [ih _ hlt]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_wires_getD_gate (gs : List Gate) (acc : List Bool) (j : ℕ) (hj : j < gs.length)
    (hback : ∀ k ∈ gs[j].inputs, k < acc.length + j) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) acc).getD
        (acc.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun k =>
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun m => w.getD m false)]) acc).getD
          k false) := by
  induction gs generalizing acc j with
  | nil => cases hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [Nat.add_zero, List.foldl_cons, List.getElem_cons_zero] at hback ⊢
      set acc' := acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]
      have hlen : acc.length < acc'.length := by
        simp only [acc', List.length_append, List.length_singleton]; omega
      rw [foldl_wires_getD_lt gs acc' acc.length hlen]
      have hlhs : acc'.getD acc.length false = g.op.eval (g.inputs.map fun k => acc.getD k false) := by
        simp only [acc', List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
          Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
      rw [hlhs]
      congr 1
      apply List.map_congr_left
      intro k hk
      have hka : k < acc.length := hback k hk
      have hka' : k < acc'.length := by omega
      rw [foldl_wires_getD_lt gs acc' k hka']
      simp only [acc', List.getD_eq_getElem?_getD, List.getElem?_append_left hka]
    | succ j' =>
      simp only [List.foldl_cons, List.getElem_cons_succ]
      set acc' := acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]
      have hlen' : acc'.length = acc.length + 1 := by
        simp only [acc', List.length_append, List.length_singleton]
      have hj' : j' < gs.length := by simp only [List.length_cons] at hj; omega
      have hidx : acc.length + (j' + 1) = acc'.length + j' := by omega
      rw [hidx]
      apply ih acc' j' hj'
      intro k hk
      have hbk := hback k (by simpa using hk)
      omega

lemma wval_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    wval C x i = x ⟨i, hi⟩ := by
  unfold wval Circuit.wires
  have hlt : i < (List.ofFn x).length := by simp [hi]
  rw [foldl_wires_getD_lt C.gates (List.ofFn x) i hlt]
  simp [List.getD_eq_getElem?_getD, hi]

lemma gateVal_eq_wval {n : ℕ} (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    gateVal n C j x = wval C x (n + j) := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  unfold gateAt
  simp [List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma gate_inputs_eq {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
  have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 _ (gateAt_mem hj)
  unfold opnd
  match h : (gateAt C j).inputs with
  | [a, b] => simp
  | [] => rw [h] at hlen; simp at hlen
  | [_] => rw [h] at hlen; simp at hlen
  | _ :: _ :: _ :: _ => rw [h] at hlen; simp at hlen

lemma opnd_mem {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b ∈ (gateAt C j).inputs := by
  rw [gate_inputs_eq hAO hj]
  fin_cases b <;> simp

lemma opnd_lt {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b < n + j :=
  hAO.2.1 j hj _ (opnd_mem hAO hj b)

lemma wval_gate_eval {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) :
    wval C x (n + j) = (gateAt C j).op.eval [wval C x (opnd C j 0), wval C x (opnd C j 1)] := by
  unfold wval Circuit.wires
  have hlen : (List.ofFn x).length = n := List.length_ofFn
  have hback : ∀ k ∈ C.gates[j].inputs, k < (List.ofFn x).length + j := by
    intro k hk; rw [hlen, ← gateAt_eq hj] at *; exact hAO.2.1 j hj k hk
  have h := foldl_wires_getD_gate C.gates (List.ofFn x) j hj hback
  rw [hlen] at h
  rw [h, ← gateAt_eq hj, gate_inputs_eq hAO hj]
  simp

lemma wval_gate_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) :
    wval C x (n + j) = (wval C x (opnd C j 0) || wval C x (opnd C j 1)) := by
  rw [wval_gate_eval hAO x hj, hop]; simp [GateOp.eval]

lemma foldl_cones_len (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) :
    (gs.foldl (coneStep n) acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, coneStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_cones_getD_lt (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl (coneStep n) acc).getD i [] = acc.getD i [] := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (coneStep n acc g).length := by
      simp only [coneStep, List.length_append, List.length_singleton]; omega
    rw [ih _ hlt]
    simp only [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma cones_length (n : ℕ) (C : Circuit) : (cones n C).length = C.gates.length := by
  unfold cones; rw [foldl_cones_len]; simp

lemma foldl_cones_getD_gate (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl (coneStep n) acc).getD (acc.length + j) [] =
      (gs[j].inputs.filter (fun w => decide (n ≤ w ∧ w < n + (acc.length + j)))).flatMap
        (fun w => (w - n) :: (gs.foldl (coneStep n) acc).getD (w - n) []) := by
  induction gs generalizing acc j with
  | nil => cases hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [Nat.add_zero, List.foldl_cons, List.getElem_cons_zero]
      set acc' := coneStep n acc g
      have hlen : acc.length < acc'.length := by
        simp only [acc', coneStep, List.length_append, List.length_singleton]; omega
      rw [foldl_cones_getD_lt n gs acc' acc.length hlen]
      have hlhs : acc'.getD acc.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + acc.length))).flatMap
            (fun w => (w - n) :: acc.getD (w - n) []) := by
        simp only [acc', coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
          Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
      rw [hlhs]
      apply List.flatMap_congr
      intro w hw
      simp only [List.mem_filter, decide_eq_true_eq] at hw
      have hwn : w - n < acc.length := by omega
      have hwn' : w - n < acc'.length := by omega
      rw [foldl_cones_getD_lt n gs acc' (w - n) hwn']
      simp only [acc', coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hwn]
    | succ j' =>
      simp only [List.foldl_cons, List.getElem_cons_succ]
      set acc' := coneStep n acc g
      have hlen' : acc'.length = acc.length + 1 := by
        simp only [acc', coneStep, List.length_append, List.length_singleton]
      have hj' : j' < gs.length := by simp only [List.length_cons] at hj; omega
      have hidx : acc.length + (j' + 1) = acc'.length + j' := by omega
      rw [hidx]
      exact ih acc' j' hj'

lemma inCone_lt_len {n : ℕ} {C : Circuit} {i j : ℕ} (h : InCone n C i j) : j < C.gates.length := by
  by_contra hge
  unfold InCone at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [cones_length]; omega)] at h
  simp at h

lemma inCone_iff {n : ℕ} {C : Circuit} {i j : ℕ} (hj : j < C.gates.length) :
    InCone n C i j ↔
      ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧ (i = w - n ∨ InCone n C i (w - n)) := by
  unfold InCone cones
  have h := foldl_cones_getD_gate n C.gates [] j hj
  simp only [List.length_nil, Nat.zero_add] at h
  rw [h, ← gateAt_eq hj]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw1, hw2, hw3⟩, hw4⟩; exact ⟨w, hw1, hw2, hw3, hw4⟩
  · rintro ⟨w, hw1, hw2, hw3, hw4⟩; exact ⟨w, ⟨hw1, hw2, hw3⟩, hw4⟩

lemma inCone_trans {n : ℕ} {C : Circuit} {i j k : ℕ} (h1 : InCone n C i j) (h2 : InCone n C j k) :
    InCone n C i k := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    have hk := inCone_lt_len h2
    rw [inCone_iff hk] at h2 ⊢
    rcases h2 with ⟨w, hw, hnw, hwnk, rfl | hsub⟩
    · exact ⟨w, hw, hnw, hwnk, Or.inr h1⟩
    · exact ⟨w, hw, hnw, hwnk, Or.inr (ih (w - n) (by omega) hsub)⟩
lemma graphFun_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
  unfold graphFun; simp

lemma graphFun_unit_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) :
    graphFun G ∅ (fun w => decide (w = v)) = false := by
  rw [Bool.eq_false_iff, ne_eq, graphFun_iff]
  rintro ⟨a, b, hab, ha, hb⟩
  simp only [decide_eq_true_eq] at ha hb
  subst ha; subst hb
  exact G.loopless.irrefl _ hab

lemma input_not_belowF {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    {w : ℕ} (hw : w < n) :
    ¬ ∀ x : Fin n → Bool, wval C x w = true → graphFun G ∅ x = true := by
  intro h
  have := h (fun i => decide (i = ⟨w, hw⟩)) (by rw [wval_input C _ w hw]; simp)
  rw [graphFun_unit_false] at this
  cases this

lemma below_contains_and {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length)
    (hbelow : BelowF G C j) :
    ∃ k < C.gates.length, (gateAt C k).op = GateOp.and ∧ BelowF G C k ∧
      (k = j ∨ InCone n C k j) := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    rcases hAO.1 _ (gateAt_mem hj) with hand | hor
    · exact ⟨j, hj, hand, hbelow, Or.inl rfl⟩
    · let w := opnd C j 0
      have hw : w < n + j := opnd_lt hAO hj 0
      have hwb : ∀ x : Fin n → Bool, wval C x w = true → graphFun G ∅ x = true := by
        intro x hx
        apply hbelow x
        rw [gateVal_eq_wval, wval_gate_or hAO x hj hor, Bool.or_eq_true]
        exact Or.inl hx
      have hnw : n ≤ w := by
        by_contra hn
        exact input_not_belowF (by omega : w < n) hwb
      have heq : n + (w - n) = w := by omega
      have hwb' : BelowF G C (w - n) := by
        intro x hx
        apply hwb x
        simpa only [gateVal_eq_wval, heq] using hx
      obtain ⟨k, hk, hop, hb, hkrel⟩ := ih (w - n) (by omega) (by omega) hwb'
      refine ⟨k, hk, hop, hb, Or.inr ?_⟩
      exact (inCone_iff hj).mpr ⟨w, opnd_mem hAO hj 0, hnw, hw, hkrel⟩

lemma cone_val_mono_of_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {h j : ℕ} (hdesc : ∀ k < C.gates.length, InCone n C h k → (gateAt C k).op = GateOp.or)
    (x : Fin n → Bool) (hx : gateVal n C h x = true) (hcone : InCone n C h j) :
    gateVal n C j x = true := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    have hj := inCone_lt_len hcone
    have hor := hdesc j hj hcone
    obtain ⟨w, hwmem, hnw, hwlt, hrel⟩ := (inCone_iff hj).mp hcone
    have hwtrue : wval C x w = true := by
      have heq : n + (w - n) = w := by omega
      rcases hrel with he | hc
      · rw [← heq, ← gateVal_eq_wval, ← he]
        exact hx
      · have hp := ih (w - n) (by omega) hc
        simpa only [gateVal_eq_wval, heq] using hp
    rw [gateVal_eq_wval, wval_gate_or hAO x hj hor, Bool.or_eq_true]
    rw [gate_inputs_eq hAO hj] at hwmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hwmem
    rcases hwmem with he | he
    · exact Or.inl (he ▸ hwtrue)
    · exact Or.inr (he ▸ hwtrue)

lemma topForm_liftFixed {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (hT : TopForm G C) : IsLiftFixedPoint G C := by
  rintro ⟨h, hh, b, houtcone, hor, hnb, himp, _⟩
  let w := opnd C h b
  have hwlt : w < n + h := opnd_lt hAO hh b
  have hnw : n ≤ w := by
    by_contra hn
    exact input_not_belowF (by omega : w < n) himp
  have heq : n + (w - n) = w := by omega
  have hjb : BelowF G C (w - n) := by
    intro x hx
    apply himp x
    simpa only [gateVal_eq_wval, heq] using hx
  obtain ⟨k, hk, hand, hb, hrel⟩ := below_contains_and hAO (by omega : w - n < C.gates.length) hjb
  have hkh : InCone n C k h :=
    (inCone_iff hh).mpr ⟨w, opnd_mem hAO hh b, hnw, hwlt, hrel⟩
  have hdesc : ∀ a < C.gates.length, InCone n C h a → (gateAt C a).op = GateOp.or := by
    intro a ha hha
    rcases hAO.1 _ (gateAt_mem ha) with hao | hao
    · exact False.elim (hT k hk a ha hand hb hao (inCone_trans hkh hha))
    · exact hao
  apply hnb
  intro x hx
  have hout : wval C x C.output = true := by
    rcases houtcone.2 with he | ⟨hnout, hc⟩
    · simpa only [he, gateVal_eq_wval] using hx
    · have ht := cone_val_mono_of_or hAO hdesc x hx hc
      simpa only [gateVal_eq_wval, show n + (C.output - n) = C.output by omega] using ht
  have hf := congrFun hfun x
  change wval C x C.output = graphFun G ∅ x at hf
  exact hf ▸ hout

end NormalizationBridge


open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.Core

lemma normalized_least (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hG : G.edgeFinset.Nonempty) (hC : IsLeastAO G C) :
    ∃ D : Circuit, IsLeastAO G D ∧ D.size = C.size ∧
      (junk G D).card = (junk G C).card ∧ TopForm G D ∧ IsLiftFixedPoint G D := by
  obtain ⟨D, hD, hsize, hjunk, htop⟩ := Normalization.main_ind n G hG _ C hC rfl
  exact ⟨D, hD, hsize, hjunk, htop,
    NormalizationBridge.topForm_liftFixed hD.1 hD.2.1 htop⟩





open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership

lemma coneStep_order (n : ℕ) (cs : List (List ℕ)) (g : Gate)
    (hc : ∀ i j : ℕ, i ∈ cs.getD j [] → i < j) :
    ∀ i j : ℕ, i ∈ (coneStep n cs g).getD j [] → i < j := by
  intro i j hi
  unfold coneStep at hi
  rcases Nat.lt_trichotomy j cs.length with hj | hj | hj
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hj] at hi
    exact hc i j hi
  · subst j
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
      Nat.sub_self, List.getElem?_cons_zero, Option.getD_some] at hi
    obtain ⟨w, hw, hi⟩ := List.mem_flatMap.mp hi
    simp only [List.mem_filter, decide_eq_true_eq] at hw
    rcases List.mem_cons.mp hi with hi | hi
    · omega
    · have := hc i (w - n) hi
      omega
  · have hj' : (cs ++ [(g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) [])]).length ≤ j := by
      simp only [List.length_append, List.length_singleton]
      omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hj'] at hi
    exact False.elim (List.not_mem_nil hi)

lemma cones_fold_order (n : ℕ) (gs : List Gate) (cs : List (List ℕ))
    (hc : ∀ i j : ℕ, i ∈ cs.getD j [] → i < j) :
    ∀ i j : ℕ, i ∈ (gs.foldl (coneStep n) cs).getD j [] → i < j := by
  induction gs generalizing cs with
  | nil => exact hc
  | cons g gs ih =>
    exact ih (coneStep n cs g) (coneStep_order n cs g hc)

lemma cone_index_lt {n : ℕ} {C : Circuit} {i j : ℕ} (h : InCone n C i j) : i < j := by
  exact cones_fold_order n C.gates [] (by simp) i j h

lemma two_junk_ordered {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hj : (junk G C).card = 2) :
    ∃ g h : ℕ, g < h ∧ junk G C = {g, h} ∧
      (∀ k ∈ junk G C, ¬ InCone n C k g) ∧ ¬ InCone n C h g := by
  obtain ⟨a, b, hab, hjab⟩ := Finset.card_eq_two.mp hj
  have arrange : ∀ a b : ℕ, a < b → junk G C = {a, b} →
      ∃ g h : ℕ, g < h ∧ junk G C = {g, h} ∧
        (∀ k ∈ junk G C, ¬ InCone n C k g) ∧ ¬ InCone n C h g := by
    intro a b hab hjab
    refine ⟨a, b, hab, hjab, ?_, ?_⟩
    · intro k hk hcone
      have hlt := cone_index_lt hcone
      rw [hjab] at hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      omega
    · intro hcone
      have hlt := cone_index_lt hcone
      omega
  rcases Nat.lt_or_gt_of_ne hab with hab | hba
  · exact arrange a b hab hjab
  · exact arrange b a hba (by rw [hjab, Finset.pair_comm])

lemma mem_junk_characterization {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j : ℕ) :
    j ∈ junk G C ↔ j < C.gates.length ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = GateOp.and ∧ ¬ BelowF G C j := by
  unfold junk gatesWhere
  rw [Finset.mem_filter, Finset.mem_range]
  unfold PEqualNP.CleanedNonEdge.IsDirtyAnd PEqualNP.CleanedNonEdge.IsDirty BelowF
  constructor
  · rintro ⟨hj, hop, _, x, hx, hf⟩
    refine ⟨hj, hop, ?_⟩
    intro hb
    have := hb x hx
    simp_all
  · rintro ⟨hj, hop, hb⟩
    push Not at hb
    obtain ⟨x, hx, hf⟩ := hb
    refine ⟨hj, hop, hj, x, hx, ?_⟩
    cases h : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x <;> simp_all

lemma two_junk_nested_or_pure {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ht : TopForm G C) (hj : (junk G C).card = 2) :
    ∃ g h : ℕ, g < h ∧ junk G C = {g, h} ∧
      (∀ k < C.gates.length,
        (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = GateOp.and → ¬ InCone n C k g) ∧
      (InCone n C g h ∨ ∀ k < C.gates.length,
        (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = GateOp.and → ¬ InCone n C k h) := by
  obtain ⟨g, h, hgh, hjs, hmin, _⟩ := two_junk_ordered G C hj
  have hgm : g ∈ junk G C := by rw [hjs]; simp
  have hhm : h ∈ junk G C := by rw [hjs]; simp
  have hgp := (mem_junk_characterization G C g).mp hgm
  have hhp := (mem_junk_characterization G C h).mp hhm
  refine ⟨g, h, hgh, hjs, ?_, ?_⟩
  · intro k hk hop hc
    by_cases hb : BelowF G C k
    · exact ht k hk g hgp.1 hop hb hgp.2.1 hc
    · exact hmin k ((mem_junk_characterization G C k).mpr ⟨hk, hop, hb⟩) hc
  · by_cases hc : InCone n C g h
    · exact Or.inl hc
    · right
      intro k hk hop hkh
      by_cases hb : BelowF G C k
      · exact ht k hk h hhp.1 hop hb hhp.2.1 hkh
      · have hkm := (mem_junk_characterization G C k).mpr ⟨hk, hop, hb⟩
        rw [hjs] at hkm
        simp only [Finset.mem_insert, Finset.mem_singleton] at hkm
        rcases hkm with rfl | rfl
        · exact hc hkh
        · have := cone_index_lt hkh
          omega


namespace StructuralSemantics

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadTwo

lemma card_sdiff_eq {α : Type} [DecidableEq α] {A B : Finset α} (h : A ⊆ B) :
    (B \ A).card = B.card - A.card := by
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr h]


lemma foldl_wires_len (gs : List Gate) (acc : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc).length =
      acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_wires_getD_lt (gs : List Gate) (acc : List Bool) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) acc).getD i false =
      acc.getD i false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]).length := by
      simp only [List.length_append, List.length_singleton]; omega
    rw [ih _ hlt]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_wires_getD_gate (gs : List Gate) (acc : List Bool) (j : ℕ) (hj : j < gs.length)
    (hback : ∀ k ∈ gs[j].inputs, k < acc.length + j) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) acc).getD
        (acc.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun k =>
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun m => w.getD m false)]) acc).getD
          k false) := by
  induction gs generalizing acc j with
  | nil => cases hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [Nat.add_zero, List.foldl_cons, List.getElem_cons_zero] at hback ⊢
      set acc' := acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]
      have hlen : acc.length < acc'.length := by
        simp only [acc', List.length_append, List.length_singleton]; omega
      rw [foldl_wires_getD_lt gs acc' acc.length hlen]
      have hlhs : acc'.getD acc.length false = g.op.eval (g.inputs.map fun k => acc.getD k false) := by
        simp only [acc', List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
          Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
      rw [hlhs]
      congr 1
      apply List.map_congr_left
      intro k hk
      have hka : k < acc.length := hback k hk
      have hka' : k < acc'.length := by omega
      rw [foldl_wires_getD_lt gs acc' k hka']
      simp only [acc', List.getD_eq_getElem?_getD, List.getElem?_append_left hka]
    | succ j' =>
      simp only [List.foldl_cons, List.getElem_cons_succ]
      set acc' := acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]
      have hlen' : acc'.length = acc.length + 1 := by
        simp only [acc', List.length_append, List.length_singleton]
      have hj' : j' < gs.length := by simp only [List.length_cons] at hj; omega
      have hidx : acc.length + (j' + 1) = acc'.length + j' := by omega
      rw [hidx]
      apply ih acc' j' hj'
      intro k hk
      have hbk := hback k (by simpa using hk)
      omega

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length :=
  foldl_wires_len C.gates x

lemma wval_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    wval C x i = x ⟨i, hi⟩ := by
  unfold wval Circuit.wires
  have hlt : i < (List.ofFn x).length := by simp [hi]
  rw [foldl_wires_getD_lt C.gates (List.ofFn x) i hlt]
  simp [List.getD_eq_getElem?_getD, hi]

lemma gateVal_eq_wval {n : ℕ} (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    gateVal n C j x = wval C x (n + j) := rfl

lemma wval_ge_len {n : ℕ} (C : Circuit) (x : Fin n → Bool) {w : ℕ} (hw : n + C.gates.length ≤ w) :
    wval C x w = false := by
  unfold wval
  rw [List.getD_eq_getElem?_getD]
  have hlen : (C.wires (List.ofFn x)).length = n + C.gates.length := by
    rw [wires_length, List.length_ofFn]
  rw [List.getElem?_eq_none (by omega)]
  rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  unfold gateAt
  simp [List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma gate_inputs_eq {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
  have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 _ (gateAt_mem hj)
  unfold opnd
  match h : (gateAt C j).inputs with
  | [a, b] => simp
  | [] => rw [h] at hlen; simp at hlen
  | [_] => rw [h] at hlen; simp at hlen
  | _ :: _ :: _ :: _ => rw [h] at hlen; simp at hlen

lemma opnd_mem {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b ∈ (gateAt C j).inputs := by
  rw [gate_inputs_eq hAO hj]
  fin_cases b <;> simp

lemma opnd_lt {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b < n + j :=
  hAO.2.1 j hj _ (opnd_mem hAO hj b)

lemma wval_gate_eval {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) :
    wval C x (n + j) = (gateAt C j).op.eval [wval C x (opnd C j 0), wval C x (opnd C j 1)] := by
  unfold wval Circuit.wires
  have hlen : (List.ofFn x).length = n := List.length_ofFn
  have hback : ∀ k ∈ C.gates[j].inputs, k < (List.ofFn x).length + j := by
    intro k hk; rw [hlen, ← gateAt_eq hj] at *; exact hAO.2.1 j hj k hk
  have h := foldl_wires_getD_gate C.gates (List.ofFn x) j hj hback
  rw [hlen] at h
  rw [h, ← gateAt_eq hj, gate_inputs_eq hAO hj]
  simp

lemma wval_gate_and {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
    wval C x (n + j) = (wval C x (opnd C j 0) && wval C x (opnd C j 1)) := by
  rw [wval_gate_eval hAO x hj, hop]; simp [GateOp.eval]

lemma wval_gate_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) :
    wval C x (n + j) = (wval C x (opnd C j 0) || wval C x (opnd C j 1)) := by
  rw [wval_gate_eval hAO x hj, hop]; simp [GateOp.eval]

lemma wval_allTrue {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) :
    ∀ w < n + C.gates.length, wval C (fun _ : Fin n => true) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hwn : w < n
    · rw [wval_input C _ w hwn]
    · have hj : w - n < C.gates.length := by omega
      have hw_eq : w = n + (w - n) := by omega
      rw [hw_eq]
      have hop := hAO.1 _ (gateAt_mem hj)
      have h0 : opnd C (w - n) 0 < w := by have := opnd_lt hAO hj 0; omega
      have h1 : opnd C (w - n) 1 < w := by have := opnd_lt hAO hj 1; omega
      have hv0 := ih _ h0 (by omega)
      have hv1 := ih _ h1 (by omega)
      rcases hop with hand | hor
      · rw [wval_gate_and hAO _ hj hand, hv0, hv1]; rfl
      · rw [wval_gate_or hAO _ hj hor, hv0, hv1]; rfl

lemma wval_mono {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {x y : Fin n → Bool}
    (hxy : ∀ i : Fin n, x i = true → y i = true) :
    ∀ w : ℕ, wval C x w = true → wval C y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwx
    by_cases hwn : w < n
    · rw [wval_input C x w hwn] at hwx
      rw [wval_input C y w hwn]
      exact hxy ⟨w, hwn⟩ hwx
    · by_cases hwlen : w < n + C.gates.length
      · have hj : w - n < C.gates.length := by omega
        have hw_eq : w = n + (w - n) := by omega
        rw [hw_eq] at hwx ⊢
        have h0 : opnd C (w - n) 0 < w := by have := opnd_lt hAO hj 0; omega
        have h1 : opnd C (w - n) 1 < w := by have := opnd_lt hAO hj 1; omega
        rcases hAO.1 _ (gateAt_mem hj) with hand | hor
        · rw [wval_gate_and hAO x hj hand, Bool.and_eq_true] at hwx
          rw [wval_gate_and hAO y hj hand, Bool.and_eq_true]
          exact ⟨ih _ h0 hwx.1, ih _ h1 hwx.2⟩
        · rw [wval_gate_or hAO x hj hor, Bool.or_eq_true] at hwx
          rw [wval_gate_or hAO y hj hor, Bool.or_eq_true]
          exact hwx.imp (ih _ h0) (ih _ h1)
      · rw [wval_ge_len C x (by omega)] at hwx; cases hwx


lemma foldl_cones_len (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) :
    (gs.foldl (coneStep n) acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, coneStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_cones_getD_lt (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl (coneStep n) acc).getD i [] = acc.getD i [] := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (coneStep n acc g).length := by
      simp only [coneStep, List.length_append, List.length_singleton]; omega
    rw [ih _ hlt]
    simp only [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma cones_length (n : ℕ) (C : Circuit) : (cones n C).length = C.gates.length := by
  unfold cones; rw [foldl_cones_len]; simp

lemma foldl_cones_getD_gate (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl (coneStep n) acc).getD (acc.length + j) [] =
      (gs[j].inputs.filter (fun w => decide (n ≤ w ∧ w < n + (acc.length + j)))).flatMap
        (fun w => (w - n) :: (gs.foldl (coneStep n) acc).getD (w - n) []) := by
  induction gs generalizing acc j with
  | nil => cases hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [Nat.add_zero, List.foldl_cons, List.getElem_cons_zero]
      set acc' := coneStep n acc g
      have hlen : acc.length < acc'.length := by
        simp only [acc', coneStep, List.length_append, List.length_singleton]; omega
      rw [foldl_cones_getD_lt n gs acc' acc.length hlen]
      have hlhs : acc'.getD acc.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + acc.length))).flatMap
            (fun w => (w - n) :: acc.getD (w - n) []) := by
        simp only [acc', coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
          Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
      rw [hlhs]
      apply List.flatMap_congr
      intro w hw
      simp only [List.mem_filter, decide_eq_true_eq] at hw
      have hwn : w - n < acc.length := by omega
      have hwn' : w - n < acc'.length := by omega
      rw [foldl_cones_getD_lt n gs acc' (w - n) hwn']
      simp only [acc', coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hwn]
    | succ j' =>
      simp only [List.foldl_cons, List.getElem_cons_succ]
      set acc' := coneStep n acc g
      have hlen' : acc'.length = acc.length + 1 := by
        simp only [acc', coneStep, List.length_append, List.length_singleton]
      have hj' : j' < gs.length := by simp only [List.length_cons] at hj; omega
      have hidx : acc.length + (j' + 1) = acc'.length + j' := by omega
      rw [hidx]
      exact ih acc' j' hj'

lemma inCone_lt_len {n : ℕ} {C : Circuit} {i j : ℕ} (h : InCone n C i j) : j < C.gates.length := by
  by_contra hge
  unfold InCone at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [cones_length]; omega)] at h
  simp at h

lemma inCone_iff {n : ℕ} {C : Circuit} {i j : ℕ} (hj : j < C.gates.length) :
    InCone n C i j ↔
      ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧ (i = w - n ∨ InCone n C i (w - n)) := by
  unfold InCone cones
  have h := foldl_cones_getD_gate n C.gates [] j hj
  simp only [List.length_nil, Nat.zero_add] at h
  rw [h, ← gateAt_eq hj]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw1, hw2, hw3⟩, hw4⟩; exact ⟨w, hw1, hw2, hw3, hw4⟩
  · rintro ⟨w, hw1, hw2, hw3, hw4⟩; exact ⟨w, ⟨hw1, hw2, hw3⟩, hw4⟩

lemma inCone_lt {n : ℕ} {C : Circuit} {i j : ℕ} : InCone n C i j → i < j := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro h
    have hj := inCone_lt_len h
    rw [inCone_iff hj] at h
    rcases h with ⟨w, _, hnw, hwnj, rfl | hsub⟩
    · omega
    · have := ih (w - n) (by omega) hsub; omega

lemma inCone_trans {n : ℕ} {C : Circuit} {i j k : ℕ} (h1 : InCone n C i j) (h2 : InCone n C j k) :
    InCone n C i k := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    have hk := inCone_lt_len h2
    rw [inCone_iff hk] at h2 ⊢
    rcases h2 with ⟨w, hw, hnw, hwnk, rfl | hsub⟩
    · exact ⟨w, hw, hnw, hwnk, Or.inr h1⟩
    · exact ⟨w, hw, hnw, hwnk, Or.inr (ih (w - n) (by omega) hsub)⟩

lemma pure_wire_support {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) :
    ∀ w < n + C.gates.length,
      (∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
        w = n + k ∨ (n ≤ w ∧ InCone n C k (w - n)) → False) →
      ∃ S : Finset (Fin n), S.Nonempty ∧
        ∀ x : Fin n → Bool, wval C x w = decide (∃ u ∈ S, x u = true) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hno
    by_cases hwn : w < n
    · refine ⟨{⟨w, hwn⟩}, by simp, ?_⟩
      intro x
      rw [wval_input C x w hwn]
      simp
    · have hj : w - n < C.gates.length := by omega
      have hw_eq : w = n + (w - n) := by omega
      have hor : (gateAt C (w - n)).op = GateOp.or := by
        rcases hAO.1 _ (gateAt_mem hj) with hand | hor
        · exact False.elim (hno (w - n) hj hand (Or.inl hw_eq))
        · exact hor
      have child : ∀ b : Fin 2,
          ∃ S : Finset (Fin n), S.Nonempty ∧
            ∀ x : Fin n → Bool, wval C x (opnd C (w - n) b) =
              decide (∃ u ∈ S, x u = true) := by
        intro b
        have hlt : opnd C (w - n) b < w := by
          have := opnd_lt hAO hj b
          omega
        refine ih _ hlt (by omega) ?_
        intro k hk hand hkc
        apply hno k hk hand
        right
        refine ⟨by omega, ?_⟩
        rcases hkc with heq | ⟨hnc, hc⟩
        · apply (inCone_iff hj).mpr
          refine ⟨opnd C (w - n) b, opnd_mem hAO hj b, by omega, opnd_lt hAO hj b, ?_⟩
          left
          omega
        · apply inCone_trans hc
          apply (inCone_iff hj).mpr
          exact ⟨opnd C (w - n) b, opnd_mem hAO hj b, hnc, opnd_lt hAO hj b, Or.inl rfl⟩
      obtain ⟨S, hS, hs⟩ := child 0
      obtain ⟨T, hT, ht⟩ := child 1
      refine ⟨S ∪ T, hS.mono Finset.subset_union_left, ?_⟩
      intro x
      rw [hw_eq, wval_gate_or hAO x hj hor, hs x, ht x]
      simp only [Finset.mem_union, or_and_right, exists_or, Bool.decide_or]

lemma and_of_pure_cone {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and)
    (hpure : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ¬ InCone n C k j) :
    ∃ A B : Finset (Fin n), A.Nonempty ∧ B.Nonempty ∧
      ∀ x : Fin n → Bool, gateVal n C j x =
        (decide (∃ a ∈ A, x a = true) && decide (∃ b ∈ B, x b = true)) := by
  have child : ∀ b : Fin 2,
      ∃ S : Finset (Fin n), S.Nonempty ∧
        ∀ x : Fin n → Bool, wval C x (opnd C j b) = decide (∃ u ∈ S, x u = true) := by
    intro b
    apply pure_wire_support hAO (opnd C j b) (by have := opnd_lt hAO hj b; omega)
    intro k hk hop hkc
    apply hpure k hk hop
    rcases hkc with heq | ⟨hnc, hc⟩
    · apply (inCone_iff hj).mpr
      refine ⟨opnd C j b, opnd_mem hAO hj b, by omega, opnd_lt hAO hj b, ?_⟩
      left
      omega
    · apply inCone_trans hc
      apply (inCone_iff hj).mpr
      exact ⟨opnd C j b, opnd_mem hAO hj b, hnc, opnd_lt hAO hj b, Or.inl rfl⟩
  obtain ⟨A, hA, ha⟩ := child 0
  obtain ⟨B, hB, hb⟩ := child 1
  refine ⟨A, B, hA, hB, ?_⟩
  intro x
  rw [gateVal_eq_wval, wval_gate_and hAO x hj hand, ha x, hb x]

lemma stopped_wire_support {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (g : ℕ) :
    ∀ w < n + C.gates.length,
      (∀ k < C.gates.length, (gateAt C k).op = GateOp.and → k ≠ g →
        w = n + k ∨ (n ≤ w ∧ InCone n C k (w - n)) → False) →
      ∃ (S : Finset (Fin n)) (b : Bool),
        ∀ x : Fin n → Bool, wval C x w =
          (decide (∃ u ∈ S, x u = true) || (b && gateVal n C g x)) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hno
    by_cases hwg : w = n + g
    · refine ⟨∅, true, ?_⟩
      intro x
      simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.true_and,
        Bool.false_or, gateVal_eq_wval, hwg]
    · by_cases hwn : w < n
      · refine ⟨{⟨w, hwn⟩}, false, ?_⟩
        intro x
        rw [wval_input C x w hwn]
        simp
      · have hj : w - n < C.gates.length := by omega
        have hw_eq : w = n + (w - n) := by omega
        have hor : (gateAt C (w - n)).op = GateOp.or := by
          rcases hAO.1 _ (gateAt_mem hj) with hand | hor
          · exact False.elim (hno (w - n) hj hand (by omega) (Or.inl hw_eq))
          · exact hor
        have child : ∀ b : Fin 2,
            ∃ (S : Finset (Fin n)) (d : Bool),
              ∀ x : Fin n → Bool, wval C x (opnd C (w - n) b) =
                (decide (∃ u ∈ S, x u = true) || (d && gateVal n C g x)) := by
          intro b
          have hlt : opnd C (w - n) b < w := by
            have := opnd_lt hAO hj b
            omega
          refine ih _ hlt (by omega) ?_
          intro k hk hand hkg hkc
          apply hno k hk hand hkg
          right
          refine ⟨by omega, ?_⟩
          rcases hkc with heq | ⟨hnc, hc⟩
          · apply (inCone_iff hj).mpr
            refine ⟨opnd C (w - n) b, opnd_mem hAO hj b, by omega, opnd_lt hAO hj b, ?_⟩
            left
            omega
          · apply inCone_trans hc
            apply (inCone_iff hj).mpr
            exact ⟨opnd C (w - n) b, opnd_mem hAO hj b, hnc, opnd_lt hAO hj b, Or.inl rfl⟩
        obtain ⟨S, bS, hs⟩ := child 0
        obtain ⟨T, bT, ht⟩ := child 1
        refine ⟨S ∪ T, bS || bT, ?_⟩
        intro x
        rw [hw_eq, wval_gate_or hAO x hj hor, hs x, ht x]
        simp only [Finset.mem_union, or_and_right, exists_or, Bool.decide_or]
        cases bS <;> cases bT <;> cases hg : gateVal n C g x <;>
          simp [Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

lemma and_of_one_and_cone {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (g : ℕ) {j : ℕ} (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and)
    (hcone : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → InCone n C k j → k = g) :
    ∃ (A B : Finset (Fin n)) (a b : Bool),
      ∀ x : Fin n → Bool, gateVal n C j x =
        ((decide (∃ u ∈ A, x u = true) || (a && gateVal n C g x)) &&
         (decide (∃ u ∈ B, x u = true) || (b && gateVal n C g x))) := by
  have child : ∀ b : Fin 2,
      ∃ (S : Finset (Fin n)) (d : Bool),
        ∀ x : Fin n → Bool, wval C x (opnd C j b) =
          (decide (∃ u ∈ S, x u = true) || (d && gateVal n C g x)) := by
    intro b
    apply stopped_wire_support hAO g (opnd C j b) (by have := opnd_lt hAO hj b; omega)
    intro k hk hop hkg hkc
    apply hkg
    apply hcone k hk hop
    rcases hkc with heq | ⟨hnc, hc⟩
    · apply (inCone_iff hj).mpr
      refine ⟨opnd C j b, opnd_mem hAO hj b, by omega, opnd_lt hAO hj b, ?_⟩
      left
      omega
    · apply inCone_trans hc
      apply (inCone_iff hj).mpr
      exact ⟨opnd C j b, opnd_mem hAO hj b, hnc, opnd_lt hAO hj b, Or.inl rfl⟩
  obtain ⟨A, a, ha⟩ := child 0
  obtain ⟨B, b, hb⟩ := child 1
  refine ⟨A, B, a, b, ?_⟩
  intro x
  rw [gateVal_eq_wval, wval_gate_and hAO x hj hand, ha x, hb x]

end StructuralSemantics


open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership

lemma two_junk_normal_form {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hT : TopForm G C) (hJ : (junk G C).card = 2) :
    ∃ g h : ℕ, g < h ∧ junk G C = {g, h} ∧
      ∃ (A B R S : Finset (Fin n)) (a b : Bool), A.Nonempty ∧ B.Nonempty ∧
        (∀ x : Fin n → Bool, gateVal n C g x =
          (decide (∃ u ∈ A, x u = true) && decide (∃ u ∈ B, x u = true))) ∧
        (∀ x : Fin n → Bool, gateVal n C h x =
          ((decide (∃ u ∈ R, x u = true) || (a && gateVal n C g x)) &&
           (decide (∃ u ∈ S, x u = true) || (b && gateVal n C g x)))) := by
  obtain ⟨g, h, hgh, hjs, hgpure, _⟩ := two_junk_nested_or_pure G C hT hJ
  have hgm : g ∈ junk G C := by rw [hjs]; simp
  have hhm : h ∈ junk G C := by rw [hjs]; simp
  have hgp := (mem_junk_characterization G C g).mp hgm
  have hhp := (mem_junk_characterization G C h).mp hhm
  have hhcone : ∀ k < C.gates.length,
      (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = GateOp.and →
      InCone n C k h → k = g := by
    intro k hk hop hkh
    by_cases hb : BelowF G C k
    · exact False.elim (hT k hk h hhp.1 hop hb hhp.2.1 hkh)
    · have hkm := (mem_junk_characterization G C k).mpr ⟨hk, hop, hb⟩
      rw [hjs] at hkm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hkm
      rcases hkm with hkg | rfl
      · exact hkg
      · have := cone_index_lt hkh
        omega
  obtain ⟨A, B, hA, hB, hgfun⟩ :=
    StructuralSemantics.and_of_pure_cone hAO hgp.1 hgp.2.1 hgpure
  obtain ⟨R, S, a, b, hhfun⟩ :=
    StructuralSemantics.and_of_one_and_cone hAO g hhp.1 hhp.2.1 hhcone
  exact ⟨g, h, hgh, hjs, A, B, R, S, a, b, hA, hB, hgfun, hhfun⟩


open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity PEqualNP.EdgeOwnership PEqualNP.Core

lemma normalized_two_junk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C) (hJ : (junk G C).card = 2) :
    ∃ D : Circuit, IsLeastAO G D ∧ D.size = C.size ∧ (junk G D).card = 2 ∧
      TopForm G D ∧ IsLiftFixedPoint G D ∧
      ∃ g h : ℕ, g < h ∧ junk G D = {g, h} ∧
        ∃ (A B R S : Finset (Fin n)) (a b : Bool), A.Nonempty ∧ B.Nonempty ∧
          (∀ x : Fin n → Bool, gateVal n D g x =
            (decide (∃ u ∈ A, x u = true) && decide (∃ u ∈ B, x u = true))) ∧
          (∀ x : Fin n → Bool, gateVal n D h x =
            ((decide (∃ u ∈ R, x u = true) || (a && gateVal n D g x)) &&
             (decide (∃ u ∈ S, x u = true) || (b && gateVal n D g x)))) := by
  have hjn : (junk G C).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨u, v, huv⟩ := edge_exists_of_nonempty_junk hC hjn
  have hE : G.edgeFinset.Nonempty := ⟨s(u, v), by simpa using huv⟩
  obtain ⟨D, hD, hsize, hjunk, htop, hfixed⟩ := normalized_least n G C hE hC
  have hDtwo : (junk G D).card = 2 := hjunk.trans hJ
  exact ⟨D, hD, hsize, hDtwo, htop, hfixed, two_junk_normal_form G D hD.1 htop hDtwo⟩





namespace Surgery

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadTwo

lemma card_sdiff_eq {α : Type} [DecidableEq α] {A B : Finset α} (h : A ⊆ B) :
    (B \ A).card = B.card - A.card := by
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr h]

-- Section 1: Basic wire, cone, OrReaches, orIn, and side lemmas

lemma foldl_wires_len (gs : List Gate) (acc : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc).length =
      acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_wires_getD_lt (gs : List Gate) (acc : List Bool) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) acc).getD i false =
      acc.getD i false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]).length := by
      simp only [List.length_append, List.length_singleton]; omega
    rw [ih _ hlt]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_wires_getD_gate (gs : List Gate) (acc : List Bool) (j : ℕ) (hj : j < gs.length)
    (hback : ∀ k ∈ gs[j].inputs, k < acc.length + j) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) acc).getD
        (acc.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun k =>
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun m => w.getD m false)]) acc).getD
          k false) := by
  induction gs generalizing acc j with
  | nil => cases hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [Nat.add_zero, List.foldl_cons, List.getElem_cons_zero] at hback ⊢
      set acc' := acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]
      have hlen : acc.length < acc'.length := by
        simp only [acc', List.length_append, List.length_singleton]; omega
      rw [foldl_wires_getD_lt gs acc' acc.length hlen]
      have hlhs : acc'.getD acc.length false = g.op.eval (g.inputs.map fun k => acc.getD k false) := by
        simp only [acc', List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
          Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
      rw [hlhs]
      congr 1
      apply List.map_congr_left
      intro k hk
      have hka : k < acc.length := hback k hk
      have hka' : k < acc'.length := by omega
      rw [foldl_wires_getD_lt gs acc' k hka']
      simp only [acc', List.getD_eq_getElem?_getD, List.getElem?_append_left hka]
    | succ j' =>
      simp only [List.foldl_cons, List.getElem_cons_succ]
      set acc' := acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]
      have hlen' : acc'.length = acc.length + 1 := by
        simp only [acc', List.length_append, List.length_singleton]
      have hj' : j' < gs.length := by simp only [List.length_cons] at hj; omega
      have hidx : acc.length + (j' + 1) = acc'.length + j' := by omega
      rw [hidx]
      apply ih acc' j' hj'
      intro k hk
      have hbk := hback k (by simpa using hk)
      omega

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length :=
  foldl_wires_len C.gates x

lemma wval_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    wval C x i = x ⟨i, hi⟩ := by
  unfold wval Circuit.wires
  have hlt : i < (List.ofFn x).length := by simp [hi]
  rw [foldl_wires_getD_lt C.gates (List.ofFn x) i hlt]
  simp [List.getD_eq_getElem?_getD, hi]

lemma gateVal_eq_wval {n : ℕ} (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    gateVal n C j x = wval C x (n + j) := rfl

lemma wval_ge_len {n : ℕ} (C : Circuit) (x : Fin n → Bool) {w : ℕ} (hw : n + C.gates.length ≤ w) :
    wval C x w = false := by
  unfold wval
  rw [List.getD_eq_getElem?_getD]
  have hlen : (C.wires (List.ofFn x)).length = n + C.gates.length := by
    rw [wires_length, List.length_ofFn]
  rw [List.getElem?_eq_none (by omega)]
  rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  unfold gateAt
  simp [List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma gate_inputs_eq {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
  have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 _ (gateAt_mem hj)
  unfold opnd
  match h : (gateAt C j).inputs with
  | [a, b] => simp
  | [] => rw [h] at hlen; simp at hlen
  | [_] => rw [h] at hlen; simp at hlen
  | _ :: _ :: _ :: _ => rw [h] at hlen; simp at hlen

lemma opnd_mem {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b ∈ (gateAt C j).inputs := by
  rw [gate_inputs_eq hAO hj]
  fin_cases b <;> simp

lemma opnd_lt {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b < n + j :=
  hAO.2.1 j hj _ (opnd_mem hAO hj b)

lemma wval_gate_eval {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) :
    wval C x (n + j) = (gateAt C j).op.eval [wval C x (opnd C j 0), wval C x (opnd C j 1)] := by
  unfold wval Circuit.wires
  have hlen : (List.ofFn x).length = n := List.length_ofFn
  have hback : ∀ k ∈ C.gates[j].inputs, k < (List.ofFn x).length + j := by
    intro k hk; rw [hlen, ← gateAt_eq hj] at *; exact hAO.2.1 j hj k hk
  have h := foldl_wires_getD_gate C.gates (List.ofFn x) j hj hback
  rw [hlen] at h
  rw [h, ← gateAt_eq hj, gate_inputs_eq hAO hj]
  simp

lemma wval_gate_and {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
    wval C x (n + j) = (wval C x (opnd C j 0) && wval C x (opnd C j 1)) := by
  rw [wval_gate_eval hAO x hj, hop]; simp [GateOp.eval]

lemma wval_gate_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) :
    wval C x (n + j) = (wval C x (opnd C j 0) || wval C x (opnd C j 1)) := by
  rw [wval_gate_eval hAO x hj, hop]; simp [GateOp.eval]

lemma wval_allTrue {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) :
    ∀ w < n + C.gates.length, wval C (fun _ : Fin n => true) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hwn : w < n
    · rw [wval_input C _ w hwn]
    · have hj : w - n < C.gates.length := by omega
      have hw_eq : w = n + (w - n) := by omega
      rw [hw_eq]
      have hop := hAO.1 _ (gateAt_mem hj)
      have h0 : opnd C (w - n) 0 < w := by have := opnd_lt hAO hj 0; omega
      have h1 : opnd C (w - n) 1 < w := by have := opnd_lt hAO hj 1; omega
      have hv0 := ih _ h0 (by omega)
      have hv1 := ih _ h1 (by omega)
      rcases hop with hand | hor
      · rw [wval_gate_and hAO _ hj hand, hv0, hv1]; rfl
      · rw [wval_gate_or hAO _ hj hor, hv0, hv1]; rfl

lemma wval_mono {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {x y : Fin n → Bool}
    (hxy : ∀ i : Fin n, x i = true → y i = true) :
    ∀ w : ℕ, wval C x w = true → wval C y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwx
    by_cases hwn : w < n
    · rw [wval_input C x w hwn] at hwx
      rw [wval_input C y w hwn]
      exact hxy ⟨w, hwn⟩ hwx
    · by_cases hwlen : w < n + C.gates.length
      · have hj : w - n < C.gates.length := by omega
        have hw_eq : w = n + (w - n) := by omega
        rw [hw_eq] at hwx ⊢
        have h0 : opnd C (w - n) 0 < w := by have := opnd_lt hAO hj 0; omega
        have h1 : opnd C (w - n) 1 < w := by have := opnd_lt hAO hj 1; omega
        rcases hAO.1 _ (gateAt_mem hj) with hand | hor
        · rw [wval_gate_and hAO x hj hand, Bool.and_eq_true] at hwx
          rw [wval_gate_and hAO y hj hand, Bool.and_eq_true]
          exact ⟨ih _ h0 hwx.1, ih _ h1 hwx.2⟩
        · rw [wval_gate_or hAO x hj hor, Bool.or_eq_true] at hwx
          rw [wval_gate_or hAO y hj hor, Bool.or_eq_true]
          exact hwx.imp (ih _ h0) (ih _ h1)
      · rw [wval_ge_len C x (by omega)] at hwx; cases hwx

-- Cone characterization

lemma foldl_cones_len (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) :
    (gs.foldl (coneStep n) acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, coneStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_cones_getD_lt (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl (coneStep n) acc).getD i [] = acc.getD i [] := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (coneStep n acc g).length := by
      simp only [coneStep, List.length_append, List.length_singleton]; omega
    rw [ih _ hlt]
    simp only [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma cones_length (n : ℕ) (C : Circuit) : (cones n C).length = C.gates.length := by
  unfold cones; rw [foldl_cones_len]; simp

lemma foldl_cones_getD_gate (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl (coneStep n) acc).getD (acc.length + j) [] =
      (gs[j].inputs.filter (fun w => decide (n ≤ w ∧ w < n + (acc.length + j)))).flatMap
        (fun w => (w - n) :: (gs.foldl (coneStep n) acc).getD (w - n) []) := by
  induction gs generalizing acc j with
  | nil => cases hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [Nat.add_zero, List.foldl_cons, List.getElem_cons_zero]
      set acc' := coneStep n acc g
      have hlen : acc.length < acc'.length := by
        simp only [acc', coneStep, List.length_append, List.length_singleton]; omega
      rw [foldl_cones_getD_lt n gs acc' acc.length hlen]
      have hlhs : acc'.getD acc.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + acc.length))).flatMap
            (fun w => (w - n) :: acc.getD (w - n) []) := by
        simp only [acc', coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
          Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
      rw [hlhs]
      apply List.flatMap_congr
      intro w hw
      simp only [List.mem_filter, decide_eq_true_eq] at hw
      have hwn : w - n < acc.length := by omega
      have hwn' : w - n < acc'.length := by omega
      rw [foldl_cones_getD_lt n gs acc' (w - n) hwn']
      simp only [acc', coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hwn]
    | succ j' =>
      simp only [List.foldl_cons, List.getElem_cons_succ]
      set acc' := coneStep n acc g
      have hlen' : acc'.length = acc.length + 1 := by
        simp only [acc', coneStep, List.length_append, List.length_singleton]
      have hj' : j' < gs.length := by simp only [List.length_cons] at hj; omega
      have hidx : acc.length + (j' + 1) = acc'.length + j' := by omega
      rw [hidx]
      exact ih acc' j' hj'

lemma inCone_lt_len {n : ℕ} {C : Circuit} {i j : ℕ} (h : InCone n C i j) : j < C.gates.length := by
  by_contra hge
  unfold InCone at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [cones_length]; omega)] at h
  simp at h

lemma inCone_iff {n : ℕ} {C : Circuit} {i j : ℕ} (hj : j < C.gates.length) :
    InCone n C i j ↔
      ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧ (i = w - n ∨ InCone n C i (w - n)) := by
  unfold InCone cones
  have h := foldl_cones_getD_gate n C.gates [] j hj
  simp only [List.length_nil, Nat.zero_add] at h
  rw [h, ← gateAt_eq hj]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw1, hw2, hw3⟩, hw4⟩; exact ⟨w, hw1, hw2, hw3, hw4⟩
  · rintro ⟨w, hw1, hw2, hw3, hw4⟩; exact ⟨w, ⟨hw1, hw2, hw3⟩, hw4⟩

lemma inCone_lt {n : ℕ} {C : Circuit} {i j : ℕ} : InCone n C i j → i < j := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro h
    have hj := inCone_lt_len h
    rw [inCone_iff hj] at h
    rcases h with ⟨w, _, hnw, hwnj, rfl | hsub⟩
    · omega
    · have := ih (w - n) (by omega) hsub; omega

lemma inCone_trans {n : ℕ} {C : Circuit} {i j k : ℕ} (h1 : InCone n C i j) (h2 : InCone n C j k) :
    InCone n C i k := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    have hk := inCone_lt_len h2
    rw [inCone_iff hk] at h2 ⊢
    rcases h2 with ⟨w, hw, hnw, hwnk, rfl | hsub⟩
    · exact ⟨w, hw, hnw, hwnk, Or.inr h1⟩
    · exact ⟨w, hw, hnw, hwnk, Or.inr (ih (w - n) (by omega) hsub)⟩

-- OrReaches and orIn characterization

lemma foldl_orSets_len (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) :
    (gs.foldl (orStep n) acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, orStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_orSets_getD_lt (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl (orStep n) acc).getD i [] = acc.getD i [] := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (orStep n acc g).length := by
      simp only [orStep, List.length_append, List.length_singleton]; omega
    rw [ih _ hlt]
    simp only [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma orSets_length (n : ℕ) (C : Circuit) : (orSets n C).length = C.gates.length := by
  unfold orSets; rw [foldl_orSets_len]; simp

lemma foldl_orSets_getD_gate (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl (orStep n) acc).getD (acc.length + j) [] =
      (acc.length + j) :: (match gs[j].op with
        | GateOp.or =>
          (gs[j].inputs.filter (fun w => decide (n ≤ w ∧ w < n + (acc.length + j)))).flatMap
            (fun w => (gs.foldl (orStep n) acc).getD (w - n) [])
        | _ => []) := by
  induction gs generalizing acc j with
  | nil => cases hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [Nat.add_zero, List.foldl_cons, List.getElem_cons_zero]
      set acc' := orStep n acc g
      have hlen : acc.length < acc'.length := by
        simp only [acc', orStep, List.length_append, List.length_singleton]; omega
      rw [foldl_orSets_getD_lt n gs acc' acc.length hlen]
      have hlhs : acc'.getD acc.length [] =
          acc.length :: (match g.op with
            | GateOp.or =>
              (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + acc.length))).flatMap
                (fun w => acc.getD (w - n) [])
            | _ => []) := by
        simp only [acc', orStep, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
          Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
        cases g.op <;> rfl
      rw [hlhs]
      congr 1
      cases g.op
      · rfl
      · apply List.flatMap_congr
        intro w hw
        simp only [List.mem_filter, decide_eq_true_eq] at hw
        have hwn : w - n < acc.length := by omega
        have hwn' : w - n < acc'.length := by omega
        rw [foldl_orSets_getD_lt n gs acc' (w - n) hwn']
        simp only [acc', orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hwn]
      · rfl
      · rfl
      · rfl
    | succ j' =>
      simp only [List.foldl_cons, List.getElem_cons_succ]
      set acc' := orStep n acc g
      have hlen' : acc'.length = acc.length + 1 := by
        simp only [acc', orStep, List.length_append, List.length_singleton]
      have hj' : j' < gs.length := by simp only [List.length_cons] at hj; omega
      have hidx : acc.length + (j' + 1) = acc'.length + j' := by omega
      rw [hidx]
      exact ih acc' j' hj'

lemma orReaches_lt_len {n : ℕ} {C : Circuit} {w g : ℕ} (h : OrReaches n C w g) :
    w - n < C.gates.length := by
  by_contra hge
  unfold OrReaches at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [orSets_length]; omega)] at h
  simp at h

lemma orReaches_gate_iff {n : ℕ} {C : Circuit} {j g : ℕ} (hj : j < C.gates.length) :
    OrReaches n C (n + j) g ↔
      g = j ∨ ((gateAt C j).op = GateOp.or ∧
        ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧ OrReaches n C w g) := by
  unfold OrReaches orSets
  have h := foldl_orSets_getD_gate n C.gates [] j hj
  simp only [List.length_nil, Nat.zero_add] at h
  rw [Nat.add_sub_cancel_left, h, ← gateAt_eq hj]
  constructor
  · rintro ⟨_, hmem⟩
    rw [List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · exact Or.inl rfl
    · cases hop : (gateAt C j).op
      · rw [hop] at hmem; simp at hmem
      · rw [hop] at hmem
        rw [List.mem_flatMap] at hmem
        rcases hmem with ⟨w, hw, hwg⟩
        rw [List.mem_filter] at hw
        simp only [decide_eq_true_eq] at hw
        exact Or.inr ⟨rfl, w, hw.1, hw.2.1, hw.2.2, ⟨hw.2.1, hwg⟩⟩
      · rw [hop] at hmem; simp at hmem
      · rw [hop] at hmem; simp at hmem
      · rw [hop] at hmem; simp at hmem
  · rintro (rfl | ⟨hop, w, hw, hnw, hwnj, hwg⟩)
    · exact ⟨Nat.le_add_right n _, List.mem_cons_self⟩
    · refine ⟨Nat.le_add_right n j, List.mem_cons_of_mem j ?_⟩
      rw [hop, List.mem_flatMap]
      exact ⟨w, List.mem_filter.mpr ⟨hw, by simp [hnw, hwnj]⟩, hwg.2⟩

lemma orReaches_input_false {n : ℕ} {C : Circuit} {w g : ℕ} (hw : w < n) : ¬ OrReaches n C w g :=
  fun h => by have := h.1; omega

lemma orReaches_le {n : ℕ} {C : Circuit} {w g : ℕ} (h : OrReaches n C w g) : g ≤ w - n := by
  have hnw : n ≤ w := h.1
  have hj : w - n < C.gates.length := orReaches_lt_len h
  obtain ⟨k, hk⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
  subst hk
  rw [Nat.add_sub_cancel_left] at hj ⊢
  clear hnw
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    rw [orReaches_gate_iff hj] at h
    rcases h with rfl | ⟨_, u, _, hnu, hunk, hug⟩
    · exact le_refl _
    · have hlt : u - n < k := by omega
      have hu_eq : u = n + (u - n) := by omega
      rw [hu_eq] at hug
      have := ih (u - n) hlt hug (by omega)
      omega

lemma orReaches_self {n : ℕ} {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    OrReaches n C (n + j) j :=
  (orReaches_gate_iff hj).mpr (Or.inl rfl)

lemma orReaches_trans {n : ℕ} {C : Circuit} {w j g : ℕ}
    (h1 : OrReaches n C w j) (h2 : OrReaches n C (n + j) g) : OrReaches n C w g := by
  have hnw : n ≤ w := h1.1
  have hwn : w - n < C.gates.length := orReaches_lt_len h1
  obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
  rw [Nat.add_sub_cancel_left] at hwn
  clear hnw
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    rw [orReaches_gate_iff hwn] at h1
    rcases h1 with rfl | ⟨hop, u, hu, hnu, hunk, huj⟩
    · exact h2
    · rw [orReaches_gate_iff hwn]
      refine Or.inr ⟨hop, u, hu, hnu, hunk, ?_⟩
      have hu_eq : u = n + (u - n) := by omega
      rw [hu_eq] at huj ⊢
      exact ih (u - n) (by omega) huj (by omega)

lemma orReaches_inCone_or_eq {n : ℕ} {C : Circuit} {j g : ℕ} (h : OrReaches n C (n + j) g) :
    g = j ∨ InCone n C g j := by
  have hj := orReaches_lt_len h
  rw [Nat.add_sub_cancel_left] at hj
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    rw [orReaches_gate_iff hj] at h
    rcases h with rfl | ⟨_, u, hu, hnu, hunj, hug⟩
    · exact Or.inl rfl
    · right
      rw [inCone_iff hj]
      refine ⟨u, hu, hnu, hunj, ?_⟩
      have hu_eq : u = n + (u - n) := by omega
      rw [hu_eq] at hug
      exact ih (u - n) (by omega) hug (by omega)

lemma orReaches_val_mono {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {w g : ℕ} (h : OrReaches n C w g) (hg : gateVal n C g x = true) : wval C x w = true := by
  have hnw : n ≤ w := h.1
  have hwn : w - n < C.gates.length := orReaches_lt_len h
  obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
  rw [Nat.add_sub_cancel_left] at hwn
  clear hnw
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    rw [orReaches_gate_iff hwn] at h
    rcases h with rfl | ⟨hop, u, hu, hnu, hunk, hug⟩
    · exact hg
    · rw [wval_gate_or hAO x hwn hop, Bool.or_eq_true]
      rw [gate_inputs_eq hAO hwn] at hu
      have hu_eq : u = n + (u - n) := by omega
      rw [hu_eq] at hug
      have hvu := ih (u - n) (by omega) hug (by omega)
      rw [← hu_eq] at hvu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · exact Or.inl hvu
      · exact Or.inr hvu

lemma mem_orIn_input {n : ℕ} (C : Circuit) (u v : Fin n) :
    u ∈ orIn n C v.val ↔ u = v := by
  unfold orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (heq | ⟨k, _, hreach, _, _⟩)
    · exact Fin.ext heq
    · exact absurd hreach (orReaches_input_false v.isLt)
  · rintro rfl; exact Or.inl rfl

lemma orIn_and_eq_empty {n : ℕ} {C : Circuit} {j : ℕ} (hj : j < C.gates.length)
    (hand : (gateAt C j).op = GateOp.and) : orIn n C (n + j) = ∅ := by
  ext u
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, not_or]
  refine ⟨by have := u.isLt; omega, ?_⟩
  rintro ⟨k, hk, hreach, hor, _⟩
  rw [orReaches_gate_iff hj] at hreach
  rcases hreach with rfl | ⟨hor', _⟩
  · rw [hand] at hor; cases hor
  · rw [hand] at hor'; cases hor'

lemma orIn_or_eq_union {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length)
    (hor : (gateAt C j).op = GateOp.or) :
    orIn n C (n + j) = orIn n C (opnd C j 0) ∪ orIn n C (opnd C j 1) := by
  ext u
  simp only [Finset.mem_union, orIn, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (hu | ⟨k, hk, hreach, hork, huk⟩)
    · omega
    · rw [orReaches_gate_iff hj] at hreach
      rcases hreach with rfl | ⟨_, w, hw, hnw, hwnj, hwk⟩
      · rw [gate_inputs_eq hAO hj] at huk
        simp only [List.mem_cons, List.not_mem_nil, or_false] at huk
        rcases huk with h0 | h1
        · exact Or.inl (Or.inl h0)
        · exact Or.inr (Or.inl h1)
      · rw [gate_inputs_eq hAO hj] at hw
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact Or.inl (Or.inr ⟨k, hk, hwk, hork, huk⟩)
        · exact Or.inr (Or.inr ⟨k, hk, hwk, hork, huk⟩)
  · rintro ((h0 | ⟨k, hk, hwk, hork, huk⟩) | (h1 | ⟨k, hk, hwk, hork, huk⟩))
    · right
      refine ⟨j, hj, orReaches_self hj, hor, ?_⟩
      rw [gate_inputs_eq hAO hj, h0]; simp
    · right
      refine ⟨k, hk, (orReaches_gate_iff hj).mpr (Or.inr ⟨hor, opnd C j 0, opnd_mem hAO hj 0, hwk.1,
        opnd_lt hAO hj 0, hwk⟩), hork, huk⟩
    · right
      refine ⟨j, hj, orReaches_self hj, hor, ?_⟩
      rw [gate_inputs_eq hAO hj, h1]; simp
    · right
      refine ⟨k, hk, (orReaches_gate_iff hj).mpr (Or.inr ⟨hor, opnd C j 1, opnd_mem hAO hj 1, hwk.1,
        opnd_lt hAO hj 1, hwk⟩), hork, huk⟩

lemma orIn_val_mono {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {w : ℕ} {u : Fin n} (hu : u ∈ orIn n C w) (hx : x u = true) : wval C x w = true := by
  unfold orIn at hu
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
  rcases hu with rfl | ⟨k, hk, hreach, hork, huk⟩
  · rw [wval_input C x u.val u.isLt]; exact hx
  · apply orReaches_val_mono hAO x hreach
    rw [gateVal_eq_wval, wval_gate_or hAO x hk hork, Bool.or_eq_true]
    rw [gate_inputs_eq hAO hk] at huk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at huk
    rcases huk with h0 | h1
    · left; rw [← h0, wval_input C x u.val u.isLt]; exact hx
    · right; rw [← h1, wval_input C x u.val u.isLt]; exact hx

lemma orIn_subset_of_orReaches {n : ℕ} {C : Circuit} {w k : ℕ} (h : OrReaches n C w k) :
    orIn n C (n + k) ⊆ orIn n C w := by
  intro u hu
  unfold orIn at hu ⊢
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
  rcases hu with hu | ⟨m, hm, hkm, horm, hum⟩
  · omega
  · exact Or.inr ⟨m, hm, orReaches_trans h hkm, horm, hum⟩

-- Section 2: Gate deletion and structure from IsLeastAO and IsLiftFixedPoint

def delWire (n j r w : ℕ) : ℕ :=
  if w = n + j then r else if n + j < w then w - 1 else w

def delCircuit (n : ℕ) (C : Circuit) (j r : ℕ) : Circuit :=
  { gates := (C.gates.eraseIdx j).map (fun g => { g with inputs := g.inputs.map (delWire n j r) })
    output := delWire n j r C.output }

lemma delCircuit_len (n : ℕ) (C : Circuit) {j : ℕ} (hj : j < C.gates.length) (r : ℕ) :
    (delCircuit n C j r).gates.length = C.gates.length - 1 := by
  simp [delCircuit, List.length_eraseIdx, hj]

lemma delCircuit_gateAt_lt {n : ℕ} {C : Circuit} {j r i : ℕ}
    (hj : j < C.gates.length) (hi : i < j) :
    gateAt (delCircuit n C j r) i =
      { (gateAt C i) with inputs := (gateAt C i).inputs.map (delWire n j r) } := by
  have hi' : i < (delCircuit n C j r).gates.length := by rw [delCircuit_len n C hj r]; omega
  rw [gateAt_eq hi', gateAt_eq (by omega)]
  simp only [delCircuit, List.getElem_map]
  rw [List.getElem_eraseIdx_of_lt (by rw [List.length_eraseIdx, if_pos hj]; omega) hi]

lemma delCircuit_gateAt_ge {n : ℕ} {C : Circuit} {j r i : ℕ}
    (hj : j < C.gates.length) (hji : j ≤ i) (hi : i < C.gates.length - 1) :
    gateAt (delCircuit n C j r) i =
      { (gateAt C (i + 1)) with inputs := (gateAt C (i + 1)).inputs.map (delWire n j r) } := by
  have hi' : i < (delCircuit n C j r).gates.length := by rw [delCircuit_len n C hj r]; omega
  rw [gateAt_eq hi', gateAt_eq (by omega)]
  simp only [delCircuit, List.getElem_map]
  rw [List.getElem_eraseIdx_of_ge (by rw [List.length_eraseIdx, if_pos hj]; omega) hji]

lemma delCircuit_isAO2 {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j r : ℕ}
    (hj : j < C.gates.length) (hr : r < n + j) : IsAO2 n (delCircuit n C j r) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [delCircuit, List.mem_map] at hg
    rcases hg with ⟨g0, hg0, rfl⟩
    exact hAO.1 g0 (List.mem_of_mem_eraseIdx hg0)
  · intro i hi w hw
    rw [delCircuit_len n C hj r] at hi
    by_cases hij : i < j
    · rw [delCircuit_gateAt_lt hj hij] at hw
      simp only [List.mem_map] at hw
      rcases hw with ⟨u, hu, rfl⟩
      have hult : u < n + i := hAO.2.1 i (by omega) u hu
      unfold delWire
      rw [if_neg (by omega), if_neg (by omega)]
      exact hult
    · rw [delCircuit_gateAt_ge hj (by omega) hi] at hw
      simp only [List.mem_map] at hw
      rcases hw with ⟨u, hu, rfl⟩
      have hult : u < n + (i + 1) := hAO.2.1 (i + 1) (by omega) u hu
      unfold delWire
      split_ifs <;> omega
  · intro g hg
    simp only [delCircuit, List.mem_map] at hg
    rcases hg with ⟨g0, hg0, rfl⟩
    simp only [List.length_map]
    exact hAO.2.2 g0 (List.mem_of_mem_eraseIdx hg0)

lemma delCircuit_opnd_lt {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j r i : ℕ}
    (hj : j < C.gates.length) (hi : i < j) (b : Fin 2) :
    opnd (delCircuit n C j r) i b = delWire n j r (opnd C i b) := by
  unfold opnd
  rw [delCircuit_gateAt_lt hj hi, gate_inputs_eq hAO (by omega)]
  fin_cases b <;> rfl

lemma delCircuit_opnd_ge {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j r i : ℕ}
    (hj : j < C.gates.length) (hji : j ≤ i) (hi : i < C.gates.length - 1) (b : Fin 2) :
    opnd (delCircuit n C j r) i b = delWire n j r (opnd C (i + 1) b) := by
  unfold opnd
  rw [delCircuit_gateAt_ge hj hji hi, gate_inputs_eq hAO (by omega)]
  fin_cases b <;> rfl

lemma delCircuit_wval_eq {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j r : ℕ} (hj : j < C.gates.length) (hr : r < n + j)
    (heq : wval C x r = wval C x (n + j)) :
    ∀ w < n + C.gates.length, wval (delCircuit n C j r) x (delWire n j r w) = wval C x w := by
  have hAO' := delCircuit_isAO2 hAO hj hr
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hwn : w < n
    · have hdw : delWire n j r w = w := by unfold delWire; rw [if_neg (by omega), if_neg (by omega)]
      rw [hdw, wval_input _ x w hwn, wval_input _ x w hwn]
    · by_cases hwj : w = n + j
      · subst hwj
        have hdw : delWire n j r (n + j) = r := by unfold delWire; simp
        have hdr : delWire n j r r = r := by unfold delWire; rw [if_neg (by omega), if_neg (by omega)]
        have h1 := ih r hr (by omega)
        rw [hdr] at h1
        rw [hdw, h1, heq]
      · by_cases hlt : w < n + j
        · have hk : w - n < j := by omega
          have hdw : delWire n j r w = n + (w - n) := by
            unfold delWire; rw [if_neg hwj, if_neg (by omega)]; omega
          have hw_eq : w = n + (w - n) := by omega
          rw [hdw]
          conv_rhs => rw [hw_eq]
          have hk' : w - n < (delCircuit n C j r).gates.length := by rw [delCircuit_len n C hj r]; omega
          rw [wval_gate_eval hAO' x hk', wval_gate_eval hAO x (by omega)]
          have hg := delCircuit_gateAt_lt (n := n) (r := r) hj hk
          rw [delCircuit_opnd_lt hAO hj hk 0, delCircuit_opnd_lt hAO hj hk 1]
          have h0 := ih (opnd C (w - n) 0) (by have := opnd_lt hAO (by omega : w - n < C.gates.length) 0; omega) (by have := opnd_lt hAO (by omega : w - n < C.gates.length) 0; omega)
          have h1 := ih (opnd C (w - n) 1) (by have := opnd_lt hAO (by omega : w - n < C.gates.length) 1; omega) (by have := opnd_lt hAO (by omega : w - n < C.gates.length) 1; omega)
          rw [h0, h1, hg]
        · have hgt : n + j < w := by omega
          have hk : w - n - 1 < C.gates.length - 1 := by omega
          have hjk : j ≤ w - n - 1 := by omega
          have hdw : delWire n j r w = n + (w - n - 1) := by
            unfold delWire; rw [if_neg hwj, if_pos hgt]; omega
          have hw_eq : w = n + (w - n - 1 + 1) := by omega
          rw [hdw]
          conv_rhs => rw [hw_eq]
          have hk' : w - n - 1 < (delCircuit n C j r).gates.length := by rw [delCircuit_len n C hj r]; omega
          rw [wval_gate_eval hAO' x hk', wval_gate_eval hAO x (by omega)]
          have hg := delCircuit_gateAt_ge (n := n) (r := r) hj hjk hk
          rw [delCircuit_opnd_ge hAO hj hjk hk 0, delCircuit_opnd_ge hAO hj hjk hk 1]
          have h0 := ih (opnd C (w - n - 1 + 1) 0) (by have := opnd_lt hAO (by omega : w - n - 1 + 1 < C.gates.length) 0; omega) (by have := opnd_lt hAO (by omega : w - n - 1 + 1 < C.gates.length) 0; omega)
          have h1 := ih (opnd C (w - n - 1 + 1) 1) (by have := opnd_lt hAO (by omega : w - n - 1 + 1 < C.gates.length) 1; omega) (by have := opnd_lt hAO (by omega : w - n - 1 + 1 < C.gates.length) 1; omega)
          rw [h0, h1, hg]

lemma delCircuit_wval_ge {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j r : ℕ} (hj : j < C.gates.length) (hr : r < n + j)
    (hle : wval C x (n + j) = true → wval C x r = true) :
    ∀ w < n + C.gates.length, wval C x w = true → wval (delCircuit n C j r) x (delWire n j r w) = true := by
  have hAO' := delCircuit_isAO2 hAO hj hr
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hval
    by_cases hwn : w < n
    · have hdw : delWire n j r w = w := by unfold delWire; rw [if_neg (by omega), if_neg (by omega)]
      rw [hdw, wval_input _ x w hwn]; rw [wval_input _ x w hwn] at hval; exact hval
    · by_cases hwj : w = n + j
      · subst hwj
        have hdw : delWire n j r (n + j) = r := by unfold delWire; simp
        have hdr : delWire n j r r = r := by unfold delWire; rw [if_neg (by omega), if_neg (by omega)]
        have h1 := ih r hr (by omega) (hle hval)
        rw [hdr] at h1
        rw [hdw]
        exact h1
      · by_cases hlt : w < n + j
        · have hk : w - n < j := by omega
          have hdw : delWire n j r w = n + (w - n) := by
            unfold delWire; rw [if_neg hwj, if_neg (by omega)]; omega
          have hw_eq : w = n + (w - n) := by omega
          rw [hdw]; rw [hw_eq] at hval
          have hk' : w - n < (delCircuit n C j r).gates.length := by rw [delCircuit_len n C hj r]; omega
          have hg := delCircuit_gateAt_lt (n := n) (r := r) hj hk
          have h0lt : opnd C (w - n) 0 < w := by have := opnd_lt hAO (by omega : w - n < C.gates.length) 0; omega
          have h1lt : opnd C (w - n) 1 < w := by have := opnd_lt hAO (by omega : w - n < C.gates.length) 1; omega
          rcases hAO.1 _ (gateAt_mem (by omega : w - n < C.gates.length)) with hand | hor
          · rw [wval_gate_and hAO x (by omega) hand, Bool.and_eq_true] at hval
            rw [wval_gate_and hAO' x hk' (by rw [hg]; exact hand), Bool.and_eq_true]
            rw [delCircuit_opnd_lt hAO hj hk 0, delCircuit_opnd_lt hAO hj hk 1]
            exact ⟨ih _ h0lt (by omega) hval.1, ih _ h1lt (by omega) hval.2⟩
          · rw [wval_gate_or hAO x (by omega) hor, Bool.or_eq_true] at hval
            rw [wval_gate_or hAO' x hk' (by rw [hg]; exact hor), Bool.or_eq_true]
            rw [delCircuit_opnd_lt hAO hj hk 0, delCircuit_opnd_lt hAO hj hk 1]
            exact hval.imp (ih _ h0lt (by omega)) (ih _ h1lt (by omega))
        · have hgt : n + j < w := by omega
          have hk : w - n - 1 < C.gates.length - 1 := by omega
          have hjk : j ≤ w - n - 1 := by omega
          have hdw : delWire n j r w = n + (w - n - 1) := by
            unfold delWire; rw [if_neg hwj, if_pos hgt]; omega
          have hw_eq : w = n + (w - n - 1 + 1) := by omega
          rw [hdw]; rw [hw_eq] at hval
          have hk' : w - n - 1 < (delCircuit n C j r).gates.length := by rw [delCircuit_len n C hj r]; omega
          have hg := delCircuit_gateAt_ge (n := n) (r := r) hj hjk hk
          have h0lt : opnd C (w - n - 1 + 1) 0 < w := by have := opnd_lt hAO (by omega : w - n - 1 + 1 < C.gates.length) 0; omega
          have h1lt : opnd C (w - n - 1 + 1) 1 < w := by have := opnd_lt hAO (by omega : w - n - 1 + 1 < C.gates.length) 1; omega
          rcases hAO.1 _ (gateAt_mem (by omega : w - n - 1 + 1 < C.gates.length)) with hand | hor
          · rw [wval_gate_and hAO x (by omega) hand, Bool.and_eq_true] at hval
            rw [wval_gate_and hAO' x hk' (by rw [hg]; exact hand), Bool.and_eq_true]
            rw [delCircuit_opnd_ge hAO hj hjk hk 0, delCircuit_opnd_ge hAO hj hjk hk 1]
            exact ⟨ih _ h0lt (by omega) hval.1, ih _ h1lt (by omega) hval.2⟩
          · rw [wval_gate_or hAO x (by omega) hor, Bool.or_eq_true] at hval
            rw [wval_gate_or hAO' x hk' (by rw [hg]; exact hor), Bool.or_eq_true]
            rw [delCircuit_opnd_ge hAO hj hjk hk 0, delCircuit_opnd_ge hAO hj hjk hk 1]
            exact hval.imp (ih _ h0lt (by omega)) (ih _ h1lt (by omega))

lemma delCircuit_wval_not_inCone {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j r : ℕ} (hj : j < C.gates.length) (hr : r < n + j) :
    ∀ w < n + C.gates.length, w ≠ n + j → (n ≤ w → ¬ InCone n C j (w - n)) →
      wval (delCircuit n C j r) x (delWire n j r w) = wval C x w := by
  have hAO' := delCircuit_isAO2 hAO hj hr
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hwj hnc
    by_cases hwn : w < n
    · have hdw : delWire n j r w = w := by unfold delWire; rw [if_neg (by omega), if_neg (by omega)]
      rw [hdw, wval_input _ x w hwn, wval_input _ x w hwn]
    · have hnc' : ¬ InCone n C j (w - n) := hnc (by omega)
      have hop_ok : ∀ b : Fin 2, opnd C (w - n) b ≠ n + j ∧
          (n ≤ opnd C (w - n) b → ¬ InCone n C j (opnd C (w - n) b - n)) := by
        intro b
        have hk : w - n < C.gates.length := by omega
        have hmem := opnd_mem hAO hk b
        have hlt := opnd_lt hAO hk b
        constructor
        · intro heq; apply hnc'; rw [inCone_iff hk]
          exact ⟨opnd C (w - n) b, hmem, by omega, hlt, Or.inl (by omega)⟩
        · intro hnu hin; apply hnc'; rw [inCone_iff hk]
          exact ⟨opnd C (w - n) b, hmem, hnu, hlt, Or.inr hin⟩
      by_cases hlt : w < n + j
      · have hk : w - n < j := by omega
        have hdw : delWire n j r w = n + (w - n) := by
          unfold delWire; rw [if_neg hwj, if_neg (by omega)]; omega
        have hw_eq : w = n + (w - n) := by omega
        rw [hdw]
        conv_rhs => rw [hw_eq]
        have hk' : w - n < (delCircuit n C j r).gates.length := by rw [delCircuit_len n C hj r]; omega
        rw [wval_gate_eval hAO' x hk', wval_gate_eval hAO x (by omega)]
        have hg := delCircuit_gateAt_lt (n := n) (r := r) hj hk
        rw [delCircuit_opnd_lt hAO hj hk 0, delCircuit_opnd_lt hAO hj hk 1]
        have h0 := ih (opnd C (w - n) 0) (by have := opnd_lt hAO (by omega : w - n < C.gates.length) 0; omega)
          (by have := opnd_lt hAO (by omega : w - n < C.gates.length) 0; omega) (hop_ok 0).1 (hop_ok 0).2
        have h1 := ih (opnd C (w - n) 1) (by have := opnd_lt hAO (by omega : w - n < C.gates.length) 1; omega)
          (by have := opnd_lt hAO (by omega : w - n < C.gates.length) 1; omega) (hop_ok 1).1 (hop_ok 1).2
        rw [h0, h1, hg]
      · have hgt : n + j < w := by omega
        have hk : w - n - 1 < C.gates.length - 1 := by omega
        have hjk : j ≤ w - n - 1 := by omega
        have hdw : delWire n j r w = n + (w - n - 1) := by
          unfold delWire; rw [if_neg hwj, if_pos hgt]; omega
        have hw_eq : w = n + (w - n - 1 + 1) := by omega
        have hidx : w - n = w - n - 1 + 1 := by omega
        rw [hdw]
        conv_rhs => rw [hw_eq]
        have hk' : w - n - 1 < (delCircuit n C j r).gates.length := by rw [delCircuit_len n C hj r]; omega
        rw [wval_gate_eval hAO' x hk', wval_gate_eval hAO x (by omega)]
        have hg := delCircuit_gateAt_ge (n := n) (r := r) hj hjk hk
        rw [delCircuit_opnd_ge hAO hj hjk hk 0, delCircuit_opnd_ge hAO hj hjk hk 1]
        have h0 := ih (opnd C (w - n - 1 + 1) 0)
          (by have := opnd_lt hAO (by omega : w - n - 1 + 1 < C.gates.length) 0; omega)
          (by have := opnd_lt hAO (by omega : w - n - 1 + 1 < C.gates.length) 0; omega)
          (by rw [← hidx]; exact (hop_ok 0).1) (by rw [← hidx]; exact (hop_ok 0).2)
        have h1 := ih (opnd C (w - n - 1 + 1) 1)
          (by have := opnd_lt hAO (by omega : w - n - 1 + 1 < C.gates.length) 1; omega)
          (by have := opnd_lt hAO (by omega : w - n - 1 + 1 < C.gates.length) 1; omega)
          (by rw [← hidx]; exact (hop_ok 1).1) (by rw [← hidx]; exact (hop_ok 1).2)
        rw [h0, h1, hg]

-- GraphFun helpers

lemma graphFun_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
  unfold graphFun; simp

lemma graphFun_unit_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) :
    graphFun G ∅ (fun w => decide (w = v)) = false := by
  rw [Bool.eq_false_iff, ne_eq, graphFun_iff]
  rintro ⟨a, b, hab, ha, hb⟩
  simp only [decide_eq_true_eq] at ha hb
  subst ha; subst hb
  exact G.loopless.irrefl _ hab

lemma graphFun_pair_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  rw [graphFun_iff]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    unfold pairInput at ha hb
    simp only [decide_eq_true_eq] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd hab (G.loopless.irrefl _)
    · exact hab
    · exact hab.symm
    · exact absurd hab (G.loopless.irrefl _)
  · intro huv
    exact ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩

-- Consequences of IsLeastAO + IsLiftFixedPoint

lemma output_bounds {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hne : ∃ u v : Fin n, G.Adj u v) :
    n ≤ C.output ∧ C.output < n + C.gates.length := by
  obtain ⟨u, v, huv⟩ := hne
  have hfun : ∀ x, wval C x C.output = graphFun G ∅ x := fun x => congrFun hL.2.1 x
  constructor
  · by_contra hlt
    push Not at hlt
    have h1 := hfun (fun w => decide (w = ⟨C.output, hlt⟩))
    rw [wval_input C _ C.output hlt, graphFun_unit_false] at h1
    simp at h1
  · by_contra hge
    push Not at hge
    have h1 := hfun (pairInput u v)
    rw [wval_ge_len C _ hge, (graphFun_pair_iff u v).mpr huv] at h1
    cases h1

lemma least_inOutputCone {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hne : ∃ u v : Fin n, G.Adj u v) :
    ∀ j < C.gates.length, InOutputCone n C j := by
  have ⟨u, _, _⟩ := hne
  have hn0 : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) u.isLt
  have hout := output_bounds hL hne
  intro j hj
  refine ⟨hj, ?_⟩
  by_contra hnot
  push Not at hnot
  have hr : 0 < n + j := by omega
  let C' := delCircuit n C j 0
  have hAO' := delCircuit_isAO2 hL.1 hj hr
  have hfun' : circuitFun n C' = graphFun G ∅ := by
    funext x
    change wval C' x C'.output = graphFun G ∅ x
    rw [← congrFun hL.2.1 x]
    exact delCircuit_wval_not_inCone hL.1 x hj hr C.output hout.2 hnot.1 (fun _ => hnot.2 hout.1)
  have hsz := hL.2.2 C' hAO' hfun'
  simp only [Circuit.size, C', delCircuit_len n C hj 0] at hsz
  omega

lemma least_no_equiv_wire {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hne : ∃ u v : Fin n, G.Adj u v)
    {j r : ℕ} (hj : j < C.gates.length) (hr : r < n + j) :
    ¬ ∀ x : Fin n → Bool, wval C x r = wval C x (n + j) := by
  have hout := output_bounds hL hne
  intro heq
  let C' := delCircuit n C j r
  have hAO' := delCircuit_isAO2 hL.1 hj hr
  have hfun' : circuitFun n C' = graphFun G ∅ := by
    funext x
    change wval C' x C'.output = graphFun G ∅ x
    rw [← congrFun hL.2.1 x]
    exact delCircuit_wval_eq hL.1 x hj hr (heq x) C.output hout.2
  have hsz := hL.2.2 C' hAO' hfun'
  simp only [Circuit.size, C', delCircuit_len n C hj r] at hsz
  omega

lemma least_no_belowF_and_opnd {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hne : ∃ u v : Fin n, G.Adj u v)
    {a : ℕ} (ha : a < C.gates.length) (hand : (gateAt C a).op = GateOp.and) (b : Fin 2) :
    ¬ ∀ x : Fin n → Bool, wval C x (opnd C a b) = true → graphFun G ∅ x = true := by
  have hout := output_bounds hL hne
  intro hbelow
  set r := opnd C a b
  have hr : r < n + a := opnd_lt hL.1 ha b
  let C' := delCircuit n C a r
  have hAO' := delCircuit_isAO2 hL.1 ha hr
  have hfun' : circuitFun n C' = graphFun G ∅ := by
    funext x
    change wval C' x C'.output = graphFun G ∅ x
    cases hFx : graphFun G ∅ x
    · have hrx : wval C x r = false := by
        cases h : wval C x r
        · rfl
        · have := hbelow x h; rw [hFx] at this; cases this
      have hax : wval C x (n + a) = false := by
        rw [wval_gate_and hL.1 x ha hand]
        fin_cases b
        · change wval C x (opnd C a 0) = false at hrx; rw [hrx]; rfl
        · change wval C x (opnd C a 1) = false at hrx; rw [hrx, Bool.and_false]
      have hcx : wval C x C.output = false := by
        change circuitFun n C x = false; rw [congrFun hL.2.1 x]; exact hFx
      change wval (delCircuit n C a r) x (delWire n a r C.output) = false
      rw [delCircuit_wval_eq hL.1 x ha hr (by rw [hrx, hax]) C.output hout.2, hcx]
    · have hcx : wval C x C.output = true := by
        change circuitFun n C x = true; rw [congrFun hL.2.1 x]; exact hFx
      change wval (delCircuit n C a r) x (delWire n a r C.output) = true
      apply delCircuit_wval_ge hL.1 x ha hr _ C.output hout.2 hcx
      intro hax
      rw [wval_gate_and hL.1 x ha hand, Bool.and_eq_true] at hax
      fin_cases b
      · exact hax.1
      · exact hax.2
  have hsz := hL.2.2 C' hAO' hfun'
  simp only [Circuit.size, C', delCircuit_len n C ha r] at hsz
  omega

lemma input_not_belowF {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    {w : ℕ} (hw : w < n) :
    ¬ ∀ x : Fin n → Bool, wval C x w = true → graphFun G ∅ x = true := by
  intro h
  have := h (fun i => decide (i = ⟨w, hw⟩)) (by rw [wval_input C _ w hw]; simp)
  rw [graphFun_unit_false] at this
  cases this

lemma lift_no_belowF_orN_opnd {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hLift : IsLiftFixedPoint G C) (hne : ∃ u v : Fin n, G.Adj u v)
    {h : ℕ} (hh : h < C.gates.length) (hor : (gateAt C h).op = GateOp.or)
    (hnb : ¬ BelowF G C h) (b : Fin 2) :
    ¬ ∀ x : Fin n → Bool, wval C x (opnd C h b) = true → graphFun G ∅ x = true := by
  intro hbelow
  apply hLift
  refine ⟨h, hh, b, least_inOutputCone hL hne h hh, hor, hnb, hbelow, ?_⟩
  refine ⟨fun _ => true, wval_allTrue hL.1 (opnd C h b) (by have := opnd_lt hL.1 hh b; omega)⟩

lemma orT_opnds_belowF {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) {h : ℕ} (hh : h < C.gates.length)
    (hor : (gateAt C h).op = GateOp.or) (hb : BelowF G C h) (b : Fin 2) :
    n ≤ opnd C h b ∧ opnd C h b - n < C.gates.length ∧ BelowF G C (opnd C h b - n) := by
  have hwb : ∀ x, wval C x (opnd C h b) = true → graphFun G ∅ x = true := by
    intro x hwx
    apply hb x
    rw [gateVal_eq_wval, wval_gate_or hL.1 x hh hor, Bool.or_eq_true]
    fin_cases b
    · exact Or.inl hwx
    · exact Or.inr hwx
  have hge : n ≤ opnd C h b := by
    by_contra hlt; push Not at hlt; exact input_not_belowF hlt hwb
  have hlt : opnd C h b < n + h := opnd_lt hL.1 hh b
  refine ⟨hge, by omega, ?_⟩
  intro x hx
  apply hwb x
  rw [gateVal_eq_wval] at hx
  rwa [show n + (opnd C h b - n) = opnd C h b by omega] at hx

lemma mem_tops_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {k : ℕ} :
    k ∈ tops G C ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧ BelowF G C k := by
  letI : DecidableEq GateOp := gateOpDecEq
  unfold tops gatesWhere; rw [Finset.mem_filter, Finset.mem_range]

lemma mem_orT_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {k : ℕ} :
    k ∈ orT G C ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧ BelowF G C k := by
  letI : DecidableEq GateOp := gateOpDecEq
  unfold orT gatesWhere; rw [Finset.mem_filter, Finset.mem_range]

lemma mem_orN_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {k : ℕ} :
    k ∈ orN G C ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧ ¬ BelowF G C k := by
  letI : DecidableEq GateOp := gateOpDecEq
  unfold orN gatesWhere; rw [Finset.mem_filter, Finset.mem_range]

lemma mem_junk_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {k : ℕ} :
    k ∈ junk G C ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧ ¬ BelowF G C k := by
  unfold junk gatesWhere
  rw [Finset.mem_filter, Finset.mem_range]
  unfold IsDirtyAnd IsDirty BelowF
  constructor
  · rintro ⟨hk, hand, _, x, hgx, hfx⟩
    refine ⟨hk, hand, fun hb => ?_⟩
    have := hb x hgx; rw [hfx] at this; cases this
  · rintro ⟨hk, hand, hnb⟩
    push Not at hnb
    rcases hnb with ⟨x, hgx, hfx⟩
    refine ⟨hk, hand, hk, x, hgx, ?_⟩
    cases h : graphFun G ∅ x
    · rfl
    · exact absurd h hfx

lemma belowF_reader_is_orT {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hLift : IsLiftFixedPoint G C) (hne : ∃ u v : Fin n, G.Adj u v)
    {k m : ℕ} (hk : k < C.gates.length) (hbk : BelowF G C k)
    (hm : m < C.gates.length) (hread : n + k ∈ (gateAt C m).inputs) :
    m ∈ orT G C := by
  have hwb : ∀ x, wval C x (n + k) = true → graphFun G ∅ x = true := hbk
  rw [gate_inputs_eq hL.1 hm] at hread
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hread
  obtain ⟨b, hb⟩ : ∃ b : Fin 2, opnd C m b = n + k := by
    rcases hread with h0 | h1
    · exact ⟨0, h0.symm⟩
    · exact ⟨1, h1.symm⟩
  rcases hL.1.1 _ (gateAt_mem hm) with hand | hor
  · exfalso
    exact least_no_belowF_and_opnd hL hne hm hand b (by rw [hb]; exact hwb)
  · rw [mem_orT_iff]
    refine ⟨hm, hor, ?_⟩
    by_contra hnb
    exact lift_no_belowF_orN_opnd hL hLift hne hm hor hnb b (by rw [hb]; exact hwb)

lemma output_gate_mem_tops_or_orT {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) (hne : ∃ u v : Fin n, G.Adj u v) :
    C.output - n ∈ tops G C ∪ orT G C := by
  have hout := output_bounds hL hne
  have hk : C.output - n < C.gates.length := by omega
  have hb : BelowF G C (C.output - n) := by
    intro x hx
    rw [gateVal_eq_wval, show n + (C.output - n) = C.output by omega] at hx
    rw [← congrFun hL.2.1 x]; exact hx
  rw [Finset.mem_union, mem_tops_iff, mem_orT_iff]
  rcases hL.1.1 _ (gateAt_mem hk) with hand | hor
  · exact Or.inl ⟨hk, hand, hb⟩
  · exact Or.inr ⟨hk, hor, hb⟩

lemma exists_reader_of_inCone {n : ℕ} {C : Circuit} {k j : ℕ} (h : InCone n C k j) :
    ∃ m < C.gates.length, n + k ∈ (gateAt C m).inputs := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    have hj := inCone_lt_len h
    rw [inCone_iff hj] at h
    rcases h with ⟨w, hw, hnw, hwnj, rfl | hsub⟩
    · exact ⟨j, hj, by rwa [show n + (w - n) = w by omega]⟩
    · exact ih (w - n) (by omega) hsub

lemma tops_le_orT_add_one {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hLift : IsLiftFixedPoint G C) (hne : ∃ u v : Fin n, G.Adj u v) :
    (tops G C).card ≤ (orT G C).card + 1 := by
  have hout := output_bounds hL hne
  have hout_mem := output_gate_mem_tops_or_orT hL hne
  have hdisj : Disjoint (tops G C) (orT G C) := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    rw [mem_tops_iff] at hk1; rw [mem_orT_iff] at hk2
    rw [hk1.2.1] at hk2; cases hk2.2.1
  let S := ((tops G C ∪ orT G C).erase (C.output - n)).image (fun k => n + k)
  let T := (orT G C ×ˢ (Finset.univ : Finset (Fin 2))).image (fun p => opnd C p.1 p.2)
  have hsub : S ⊆ T := by
    intro w hw
    simp only [S, Finset.mem_image, Finset.mem_erase, Finset.mem_union] at hw
    rcases hw with ⟨k, ⟨hne_out, hk_mem⟩, rfl⟩
    have hk_lt : k < C.gates.length := by
      rcases hk_mem with h | h
      · exact (mem_tops_iff.mp h).1
      · exact (mem_orT_iff.mp h).1
    have hk_bf : BelowF G C k := by
      rcases hk_mem with h | h
      · exact (mem_tops_iff.mp h).2.2
      · exact (mem_orT_iff.mp h).2.2
    have hcone := least_inOutputCone hL hne k hk_lt
    have hin : InCone n C k (C.output - n) := by
      rcases hcone.2 with heq | ⟨_, hin⟩
      · exfalso; apply hne_out; omega
      · exact hin
    obtain ⟨m, hm, hread⟩ := exists_reader_of_inCone hin
    have hm_orT := belowF_reader_is_orT hL hLift hne hk_lt hk_bf hm hread
    rw [gate_inputs_eq hL.1 hm] at hread
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hread
    simp only [T, Finset.mem_image, Finset.mem_product, Finset.mem_univ, and_true]
    rcases hread with h0 | h1
    · exact ⟨(m, 0), hm_orT, h0.symm⟩
    · exact ⟨(m, 1), hm_orT, h1.symm⟩
  have hcardS : S.card = (tops G C).card + (orT G C).card - 1 := by
    rw [Finset.card_image_of_injective _ (fun a b h => by omega),
      Finset.card_erase_of_mem hout_mem, Finset.card_union_of_disjoint hdisj]
  have hcardT : T.card ≤ 2 * (orT G C).card := by
    calc T.card ≤ (orT G C ×ˢ (Finset.univ : Finset (Fin 2))).card := Finset.card_image_le
      _ = (orT G C).card * 2 := by simp
      _ = 2 * (orT G C).card := Nat.mul_comm _ _
  have hle := Finset.card_le_card hsub
  rw [hcardS] at hle
  omega

lemma circuit_size_partition {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) :
    C.size = (tops G C).card + (orT G C).card + (junk G C).card + (orN G C).card := by
  have hU : Finset.range C.gates.length = tops G C ∪ orT G C ∪ junk G C ∪ orN G C := by
    ext k
    simp only [Finset.mem_union, Finset.mem_range, mem_tops_iff, mem_orT_iff, mem_junk_iff, mem_orN_iff]
    constructor
    · intro hk
      rcases hL.1.1 _ (gateAt_mem hk) with hand | hor
      · by_cases hb : BelowF G C k
        · exact Or.inl (Or.inl (Or.inl ⟨hk, hand, hb⟩))
        · exact Or.inl (Or.inr ⟨hk, hand, hb⟩)
      · by_cases hb : BelowF G C k
        · exact Or.inl (Or.inl (Or.inr ⟨hk, hor, hb⟩))
        · exact Or.inr ⟨hk, hor, hb⟩
    · rintro (((⟨hk, _⟩ | ⟨hk, _⟩) | ⟨hk, _⟩) | ⟨hk, _⟩) <;> exact hk
  have hd1 : Disjoint (tops G C) (orT G C) := by
    rw [Finset.disjoint_left]; intro k h1 h2
    rw [mem_tops_iff] at h1; rw [mem_orT_iff] at h2; rw [h1.2.1] at h2; cases h2.2.1
  have hd2 : Disjoint (tops G C ∪ orT G C) (junk G C) := by
    rw [Finset.disjoint_left]; intro k h1 h2
    rw [mem_junk_iff] at h2; simp only [Finset.mem_union, mem_tops_iff, mem_orT_iff] at h1
    rcases h1 with h1 | h1 <;> exact h2.2.2 h1.2.2
  have hd3 : Disjoint (tops G C ∪ orT G C ∪ junk G C) (orN G C) := by
    rw [Finset.disjoint_left]; intro k h1 h2
    rw [mem_orN_iff] at h2; simp only [Finset.mem_union, mem_tops_iff, mem_orT_iff, mem_junk_iff] at h1
    rcases h1 with (h1 | h1) | h1
    · exact h2.2.2 h1.2.2
    · exact h2.2.2 h1.2.2
    · rw [h1.2.1] at h2; cases h2.2.1
  change C.gates.length = _
  rw [← Finset.card_range C.gates.length, hU,
    Finset.card_union_of_disjoint hd3, Finset.card_union_of_disjoint hd2,
    Finset.card_union_of_disjoint hd1]

lemma circuitFun_iff_exists_top {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hne : ∃ u v : Fin n, G.Adj u v) (x : Fin n → Bool) :
    circuitFun n C x = true ↔ ∃ a ∈ tops G C, gateVal n C a x = true := by
  have hout := output_bounds hL hne
  have hout_mem := output_gate_mem_tops_or_orT hL hne
  constructor
  · intro hcx
    have hkey : ∀ k, k ∈ tops G C ∪ orT G C → gateVal n C k x = true →
        ∃ a ∈ tops G C, gateVal n C a x = true := by
      intro k
      induction k using Nat.strong_induction_on with
      | ind k ih =>
        intro hk hvk
        rw [Finset.mem_union] at hk
        rcases hk with htop | horT
        · exact ⟨k, htop, hvk⟩
        · rw [mem_orT_iff] at horT
          rw [gateVal_eq_wval, wval_gate_or hL.1 x horT.1 horT.2.1, Bool.or_eq_true] at hvk
          rcases hvk with h0 | h1
          · obtain ⟨hge, hlt, hbf⟩ := orT_opnds_belowF hL horT.1 horT.2.1 horT.2.2 0
            have hlt_k : opnd C k 0 - n < k := by have := opnd_lt hL.1 horT.1 0; omega
            have hmem : opnd C k 0 - n ∈ tops G C ∪ orT G C := by
              rw [Finset.mem_union, mem_tops_iff, mem_orT_iff]
              rcases hL.1.1 _ (gateAt_mem hlt) with hand | hor
              · exact Or.inl ⟨hlt, hand, hbf⟩
              · exact Or.inr ⟨hlt, hor, hbf⟩
            exact ih _ hlt_k hmem (by rw [gateVal_eq_wval, show n + (opnd C k 0 - n) = opnd C k 0 by omega]; exact h0)
          · obtain ⟨hge, hlt, hbf⟩ := orT_opnds_belowF hL horT.1 horT.2.1 horT.2.2 1
            have hlt_k : opnd C k 1 - n < k := by have := opnd_lt hL.1 horT.1 1; omega
            have hmem : opnd C k 1 - n ∈ tops G C ∪ orT G C := by
              rw [Finset.mem_union, mem_tops_iff, mem_orT_iff]
              rcases hL.1.1 _ (gateAt_mem hlt) with hand | hor
              · exact Or.inl ⟨hlt, hand, hbf⟩
              · exact Or.inr ⟨hlt, hor, hbf⟩
            exact ih _ hlt_k hmem (by rw [gateVal_eq_wval, show n + (opnd C k 1 - n) = opnd C k 1 by omega]; exact h1)
    apply hkey (C.output - n) hout_mem
    rw [gateVal_eq_wval, show n + (C.output - n) = C.output by omega]
    exact hcx
  · rintro ⟨a, ha, hva⟩
    rw [mem_tops_iff] at ha
    rw [congrFun hL.2.1 x]
    exact ha.2.2 x hva

lemma not_belowF_wval_eq {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hLift : IsLiftFixedPoint G C) (hne : ∃ u v : Fin n, G.Adj u v)
    {g1 g2 : ℕ} (hjunk : ∀ k, k ∈ junk G C ↔ k = g1 ∨ k = g2) :
    ∀ w < n + C.gates.length,
      (∀ k, w = n + k → ¬ BelowF G C k) →
      ∀ x : Fin n → Bool,
        wval C x w = true ↔
          (∃ u ∈ orIn n C w, x u = true) ∨
          (OrReaches n C w g1 ∧ gateVal n C g1 x = true) ∨
          (OrReaches n C w g2 ∧ gateVal n C g2 x = true) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hnb x
    by_cases hwn : w < n
    · constructor
      · intro hwx
        left
        refine ⟨⟨w, hwn⟩, (mem_orIn_input C _ _).mpr rfl, ?_⟩
        rwa [wval_input C x w hwn] at hwx
      · rintro (⟨u, hu, hxu⟩ | ⟨hr, _⟩ | ⟨hr, _⟩)
        · have huw : u = ⟨w, hwn⟩ := (mem_orIn_input C u ⟨w, hwn⟩).mp hu
          subst huw; rw [wval_input C x w hwn]; exact hxu
        · exact absurd hr (orReaches_input_false hwn)
        · exact absurd hr (orReaches_input_false hwn)
    · have hk : w - n < C.gates.length := by omega
      have hw_eq : w = n + (w - n) := by omega
      have hnbk : ¬ BelowF G C (w - n) := hnb (w - n) hw_eq
      rcases hL.1.1 _ (gateAt_mem hk) with hand | hor
      · have hmem : w - n ∈ junk G C := mem_junk_iff.mpr ⟨hk, hand, hnbk⟩
        rw [hjunk] at hmem
        constructor
        · intro hwx
          rcases hmem with h1 | h2
          · right; left
            refine ⟨?_, ?_⟩
            · rw [hw_eq, h1]; exact orReaches_self (by omega)
            · rw [gateVal_eq_wval, ← h1, ← hw_eq]; exact hwx
          · right; right
            refine ⟨?_, ?_⟩
            · rw [hw_eq, h2]; exact orReaches_self (by omega)
            · rw [gateVal_eq_wval, ← h2, ← hw_eq]; exact hwx
        · rintro (⟨u, hu, _⟩ | ⟨hr, hvg⟩ | ⟨hr, hvg⟩)
          · rw [hw_eq, orIn_and_eq_empty hk hand] at hu; simp at hu
          · exact orReaches_val_mono hL.1 x hr hvg
          · exact orReaches_val_mono hL.1 x hr hvg
      · have hop_nb : ∀ b : Fin 2, ∀ m, opnd C (w - n) b = n + m → ¬ BelowF G C m := by
          intro b m hm hbm
          exact lift_no_belowF_orN_opnd hL hLift hne hk hor hnbk b (by rw [hm]; exact hbm)
        have hlt0 : opnd C (w - n) 0 < w := by have := opnd_lt hL.1 hk 0; omega
        have hlt1 : opnd C (w - n) 1 < w := by have := opnd_lt hL.1 hk 1; omega
        have ih0 := ih (opnd C (w - n) 0) hlt0 (by omega) (hop_nb 0) x
        have ih1 := ih (opnd C (w - n) 1) hlt1 (by omega) (hop_nb 1) x
        rw [hw_eq, wval_gate_or hL.1 x hk hor, Bool.or_eq_true, ih0, ih1,
          orIn_or_eq_union hL.1 hk hor]
        have hreach_iff : ∀ g, g = g1 ∨ g = g2 →
            (OrReaches n C (n + (w - n)) g ↔
              OrReaches n C (opnd C (w - n) 0) g ∨ OrReaches n C (opnd C (w - n) 1) g) := by
          intro g hg
          have hne_g : g ≠ w - n := by
            intro heq
            have hgj : g ∈ junk G C := (hjunk g).mpr hg
            rw [heq, mem_junk_iff] at hgj
            rw [hor] at hgj; cases hgj.2.1
          rw [orReaches_gate_iff hk]
          constructor
          · rintro (heq | ⟨_, u, hu, _, _, hug⟩)
            · exact absurd heq hne_g
            · rw [gate_inputs_eq hL.1 hk] at hu
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
              rcases hu with rfl | rfl
              · exact Or.inl hug
              · exact Or.inr hug
          · rintro (h0 | h1)
            · exact Or.inr ⟨hor, opnd C (w - n) 0, opnd_mem hL.1 hk 0, h0.1, opnd_lt hL.1 hk 0, h0⟩
            · exact Or.inr ⟨hor, opnd C (w - n) 1, opnd_mem hL.1 hk 1, h1.1, opnd_lt hL.1 hk 1, h1⟩
        rw [hreach_iff g1 (Or.inl rfl), hreach_iff g2 (Or.inr rfl)]
        constructor
        · rintro ((⟨u, hu, hxu⟩ | ⟨h1, hg1⟩ | ⟨h2, hg2⟩) | (⟨u, hu, hxu⟩ | ⟨h1, hg1⟩ | ⟨h2, hg2⟩))
          · exact Or.inl ⟨u, Finset.mem_union_left _ hu, hxu⟩
          · exact Or.inr (Or.inl ⟨Or.inl h1, hg1⟩)
          · exact Or.inr (Or.inr ⟨Or.inl h2, hg2⟩)
          · exact Or.inl ⟨u, Finset.mem_union_right _ hu, hxu⟩
          · exact Or.inr (Or.inl ⟨Or.inr h1, hg1⟩)
          · exact Or.inr (Or.inr ⟨Or.inr h2, hg2⟩)
        · rintro (⟨u, hu, hxu⟩ | ⟨h1 | h1, hg1⟩ | ⟨h2 | h2, hg2⟩)
          · rcases Finset.mem_union.mp hu with h0 | h1
            · exact Or.inl (Or.inl ⟨u, h0, hxu⟩)
            · exact Or.inr (Or.inl ⟨u, h1, hxu⟩)
          · exact Or.inl (Or.inr (Or.inl ⟨h1, hg1⟩))
          · exact Or.inr (Or.inr (Or.inl ⟨h1, hg1⟩))
          · exact Or.inl (Or.inr (Or.inr ⟨h2, hg2⟩))
          · exact Or.inr (Or.inr (Or.inr ⟨h2, hg2⟩))

-- Section 3: Graph properties, clean replacement circuit C', and master size inequality

lemma noFourCycle_unique {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (h4 : NoFourCycle G) {a b w1 w2 : Fin n} (hab : a ≠ b)
    (ha1 : G.Adj a w1) (hb1 : G.Adj b w1) (ha2 : G.Adj a w2) (hb2 : G.Adj b w2) : w1 = w2 := by
  by_contra hne
  have hle := h4 a b hab
  have hsub : ({w1, w2} : Finset (Fin n)) ⊆ Finset.univ.filter (fun w => G.Adj a w ∧ G.Adj b w) := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hw with rfl | rfl
    · exact ⟨ha1, hb1⟩
    · exact ⟨ha2, hb2⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_pair hne] at hcard
  omega

lemma top_sides_adj {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hAO : IsAO2 n C) {a : ℕ} (ha : a ∈ tops G C)
    {u v : Fin n} (hu : u ∈ side (n := n) C a 0) (hv : v ∈ side (n := n) C a 1) :
    G.Adj u v := by
  rw [mem_tops_iff] at ha
  have hval : gateVal n C a (pairInput u v) = true := by
    rw [gateVal_eq_wval, wval_gate_and hAO _ ha.1 ha.2.1, Bool.and_eq_true]
    exact ⟨orIn_val_mono hAO _ hu (by simp [pairInput]),
      orIn_val_mono hAO _ hv (by simp [pairInput])⟩
  exact (graphFun_pair_iff u v).mp (ha.2.2 (pairInput u v) hval)

lemma top_is_star {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hAO : IsAO2 n C) (h4 : NoFourCycle G) {a : ℕ} (ha : a ∈ tops G C \ centreless G C) :
    (side (n := n) C a 0).Nonempty ∧ (side (n := n) C a 1).Nonempty ∧
      ((side (n := n) C a 0).card = 1 ∨ (side (n := n) C a 1).card = 1) := by
  rw [Finset.mem_sdiff] at ha
  have hne0 : (side (n := n) C a 0).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h0; exact ha.2 (Finset.mem_filter.mpr ⟨ha.1, Or.inl h0⟩)
  have hne1 : (side (n := n) C a 1).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h1; exact ha.2 (Finset.mem_filter.mpr ⟨ha.1, Or.inr h1⟩)
  refine ⟨hne0, hne1, ?_⟩
  by_contra hboth
  push Not at hboth
  have hc0 : 1 < (side (n := n) C a 0).card := by
    have := Finset.Nonempty.card_pos hne0; omega
  have hc1 : 1 < (side (n := n) C a 1).card := by
    have := Finset.Nonempty.card_pos hne1; omega
  obtain ⟨u1, hu1, u2, hu2, hu12⟩ := Finset.one_lt_card.mp hc0
  obtain ⟨v1, hv1, v2, hv2, hv12⟩ := Finset.one_lt_card.mp hc1
  exact hv12 (noFourCycle_unique h4 hu12
    (top_sides_adj hAO ha.1 hu1 hv1) (top_sides_adj hAO ha.1 hu2 hv1)
    (top_sides_adj hAO ha.1 hu1 hv2) (top_sides_adj hAO ha.1 hu2 hv2))

-- Clean replacement circuit C' builder

lemma wval_append_lt {n : ℕ} (gs1 gs2 : List Gate) (o1 o2 : ℕ) (x : Fin n → Bool)
    {w : ℕ} (hw : w < n + gs1.length) :
    wval ⟨gs1 ++ gs2, o2⟩ x w = wval ⟨gs1, o1⟩ x w := by
  unfold wval Circuit.wires
  rw [List.foldl_append]
  have hlen : w < (gs1.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (List.ofFn x)).length := by
    rw [foldl_wires_len, List.length_ofFn]; exact hw
  exact foldl_wires_getD_lt gs2 _ w hlen

def appendOrList (n : ℕ) (gs : List Gate) : List ℕ → List Gate × ℕ
  | [] => (gs, 0)
  | [w] => (gs, w)
  | w :: w2 :: ws =>
    let res := appendOrList n gs (w2 :: ws)
    (res.1 ++ [⟨GateOp.or, [w, res.2]⟩], n + res.1.length)

lemma appendOrList_prefix (n : ℕ) (gs : List Gate) (ws : List ℕ) :
    ∃ extra : List Gate, (appendOrList n gs ws).1 = gs ++ extra := by
  match ws with
  | [] => exact ⟨[], by simp [appendOrList]⟩
  | [w] => exact ⟨[], by simp [appendOrList]⟩
  | w :: w2 :: ws =>
    obtain ⟨extra, heq⟩ := appendOrList_prefix n gs (w2 :: ws)
    refine ⟨extra ++ [⟨GateOp.or, [w, (appendOrList n gs (w2 :: ws)).2]⟩], ?_⟩
    simp only [appendOrList, heq, List.append_assoc]

lemma appendOrList_len (n : ℕ) (gs : List Gate) (ws : List ℕ) (hne : ws ≠ []) :
    (appendOrList n gs ws).1.length = gs.length + (ws.length - 1) := by
  match ws with
  | [] => exact absurd rfl hne
  | [w] => simp [appendOrList]
  | w :: w2 :: ws =>
    have ih := appendOrList_len n gs (w2 :: ws) (by simp)
    simp only [appendOrList, List.length_append, List.length_cons, List.length_nil] at ih ⊢
    omega

lemma appendOrList_isAO2 {n : ℕ} {gs : List Gate} (hAO : IsAO2 n ⟨gs, 0⟩)
    (ws : List ℕ) (hne : ws ≠ []) (hws : ∀ w ∈ ws, w < n + gs.length) :
    IsAO2 n ⟨(appendOrList n gs ws).1, 0⟩ ∧
      (appendOrList n gs ws).2 < n + (appendOrList n gs ws).1.length := by
  match ws with
  | [] => exact absurd rfl hne
  | [w] =>
    simp only [appendOrList]
    exact ⟨hAO, hws w (by simp)⟩
  | w :: w2 :: ws =>
    have ⟨hAO', hlt'⟩ := appendOrList_isAO2 hAO (w2 :: ws) (by simp) (fun u hu => hws u (by simp [hu]))
    have hglen : gs.length ≤ (appendOrList n gs (w2 :: ws)).1.length := by
      rw [appendOrList_len n gs (w2 :: ws) (by simp)]; omega
    have hwlt : w < n + (appendOrList n gs (w2 :: ws)).1.length := by have := hws w (by simp); omega
    simp only [appendOrList]
    set gs' := (appendOrList n gs (w2 :: ws)).1
    set w' := (appendOrList n gs (w2 :: ws)).2
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · intro g hg
      simp only [List.mem_append, List.mem_singleton] at hg
      rcases hg with hg | rfl
      · exact hAO'.1 g hg
      · exact Or.inr rfl
    · intro j hj u hu
      simp only [List.length_append, List.length_singleton] at hj
      by_cases hlt : j < gs'.length
      · have hgat : gateAt ⟨gs' ++ [⟨GateOp.or, [w, w']⟩], 0⟩ j = gateAt ⟨gs', 0⟩ j := by
          rw [gateAt_eq (by simp; omega), gateAt_eq hlt]
          simp [List.getElem_append_left hlt]
        rw [hgat] at hu
        exact hAO'.2.1 j hlt u hu
      · have hjeq : j = gs'.length := by omega
        subst hjeq
        have hgat : gateAt ⟨gs' ++ [⟨GateOp.or, [w, w']⟩], 0⟩ gs'.length = ⟨GateOp.or, [w, w']⟩ := by
          rw [gateAt_eq (by simp)]
          simp
        rw [hgat] at hu
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with rfl | rfl
        · exact hwlt
        · exact hlt'
    · intro g hg
      simp only [List.mem_append, List.mem_singleton] at hg
      rcases hg with hg | rfl
      · exact hAO'.2.2 g hg
      · rfl
    · simp only [List.length_append, List.length_singleton]; omega

lemma appendOrList_wval {n : ℕ} {gs : List Gate} (hAO : IsAO2 n ⟨gs, 0⟩) (x : Fin n → Bool)
    (ws : List ℕ) (hne : ws ≠ []) (hws : ∀ w ∈ ws, w < n + gs.length) :
    wval ⟨(appendOrList n gs ws).1, 0⟩ x (appendOrList n gs ws).2 =
      decide (∃ w ∈ ws, wval ⟨gs, 0⟩ x w = true) := by
  match ws with
  | [] => exact absurd rfl hne
  | [w] =>
    simp only [appendOrList, List.mem_singleton, exists_eq_left]
    cases wval ⟨gs, 0⟩ x w <;> rfl
  | w :: w2 :: ws =>
    have hrest := appendOrList_isAO2 hAO (w2 :: ws) (by simp) (fun u hu => hws u (by simp [hu]))
    have ih := appendOrList_wval hAO x (w2 :: ws) (by simp) (fun u hu => hws u (by simp [hu]))
    have hfull := appendOrList_isAO2 hAO (w :: w2 :: ws) (by simp) hws
    obtain ⟨extra, hextra⟩ := appendOrList_prefix n gs (w2 :: ws)
    simp only [appendOrList] at hfull ⊢
    set gs' := (appendOrList n gs (w2 :: ws)).1
    set w' := (appendOrList n gs (w2 :: ws)).2
    have hglen : gs.length ≤ gs'.length := by rw [hextra, List.length_append]; omega
    have hwlt : w < n + gs.length := hws w (by simp)
    have hgat : gateAt ⟨gs' ++ [⟨GateOp.or, [w, w']⟩], 0⟩ gs'.length = ⟨GateOp.or, [w, w']⟩ := by
      rw [gateAt_eq (by simp)]; simp
    have hop0 : opnd ⟨gs' ++ [⟨GateOp.or, [w, w']⟩], 0⟩ gs'.length 0 = w := by
      unfold opnd; rw [hgat]; rfl
    have hop1 : opnd ⟨gs' ++ [⟨GateOp.or, [w, w']⟩], 0⟩ gs'.length 1 = w' := by
      unfold opnd; rw [hgat]; rfl
    have hlen_lt : gs'.length < (gs' ++ [({ op := GateOp.or, inputs := [w, w'] } : Gate)]).length := by simp
    rw [wval_gate_or hfull.1 x hlen_lt (by rw [hgat]), hop0, hop1]
    rw [wval_append_lt gs' [({ op := GateOp.or, inputs := [w, w'] } : Gate)] 0 0 x (by omega),
      wval_append_lt gs' [({ op := GateOp.or, inputs := [w, w'] } : Gate)] 0 0 x hrest.2]
    have hvw : wval ⟨gs', 0⟩ x w = wval ⟨gs, 0⟩ x w := by
      rw [hextra]; exact wval_append_lt gs extra 0 0 x hwlt
    rw [hvw, ih]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.mem_cons, exists_eq_or_imp]

lemma appendGate_isAO2 {n : ℕ} {gs : List Gate} (hAO : IsAO2 n ⟨gs, 0⟩)
    {op : GateOp} (hop : op = GateOp.and ∨ op = GateOp.or)
    {w0 w1 : ℕ} (h0 : w0 < n + gs.length) (h1 : w1 < n + gs.length) :
    IsAO2 n ⟨gs ++ [⟨op, [w0, w1]⟩], 0⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hAO.1 g hg
    · exact hop
  · intro j hj u hu
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · have hgat : gateAt ⟨gs ++ [⟨op, [w0, w1]⟩], 0⟩ j = gateAt ⟨gs, 0⟩ j := by
        rw [gateAt_eq (by simp; omega), gateAt_eq hlt]; simp [List.getElem_append_left hlt]
      rw [hgat] at hu
      exact hAO.2.1 j hlt u hu
    · have hjeq : j = gs.length := by omega
      subst hjeq
      have hgat : gateAt ⟨gs ++ [⟨op, [w0, w1]⟩], 0⟩ gs.length = ⟨op, [w0, w1]⟩ := by
        rw [gateAt_eq (by simp)]; simp
      rw [hgat] at hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl <;> assumption
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hAO.2.2 g hg
    · rfl

-- Layer 1: bypass map and lamGates

def bypass (n : ℕ) (C : Circuit) (lamList : List ℕ) : ℕ → ℕ
  | w =>
    if hw : w < n then w
    else
      let k := w - n
      if hk : k < C.gates.length then
        if k ∈ lamList then n + lamList.idxOf k
        else if (orIn n C (opnd C k 0)).Nonempty then
          if hlt : opnd C k 0 < w then bypass n C lamList (opnd C k 0) else 0
        else
          if hlt : opnd C k 1 < w then bypass n C lamList (opnd C k 1) else 0
      else 0
termination_by w => w

def lamGates (n : ℕ) (C : Circuit) (lamList : List ℕ) : List Gate :=
  lamList.map fun k => ⟨GateOp.or, [bypass n C lamList (opnd C k 0), bypass n C lamList (opnd C k 1)]⟩

lemma bypass_bound {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (lamList : List ℕ)
    (hsort : lamList.Pairwise (· < ·)) :
    ∀ w < n + C.gates.length, bypass n C lamList w < n ∨
      (n ≤ w ∧ ∃ k ∈ lamList, k ≤ w - n ∧ bypass n C lamList w = n + lamList.idxOf k) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwlen
    unfold bypass
    dsimp only
    split_ifs with hw hk hmem h0 hlt0 h1
    · exact Or.inl hw
    · exact Or.inr ⟨by omega, w - n, hmem, le_refl _, rfl⟩
    · rcases ih (opnd C (w - n) 0) hlt0 (by omega) with hlt | ⟨hnle, k, hkmem, hkle, heq⟩
      · exact Or.inl hlt
      · exact Or.inr ⟨by omega, k, hkmem, by omega, heq⟩
    · exfalso; have := opnd_lt hAO hk 0; omega
    · rcases ih (opnd C (w - n) 1) h1 (by omega) with hlt | ⟨hnle, k, hkmem, hkle, heq⟩
      · exact Or.inl hlt
      · exact Or.inr ⟨by omega, k, hkmem, by omega, heq⟩
    · exfalso; have := opnd_lt hAO hk 1; omega
    · exfalso; omega

lemma idxOf_lt_of_pairwise_lt {l : List ℕ} (hsort : l.Pairwise (· < ·))
    {a b : ℕ} (ha : a ∈ l) (hb : b ∈ l) (hab : a < b) : l.idxOf a < l.idxOf b := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
    rw [List.pairwise_cons] at hsort
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · omega
    · rw [List.idxOf_cons_self]
      have hne : a ≠ b := Nat.ne_of_lt hab
      rw [List.idxOf_cons_ne _ (by simp [hne])]
      exact Nat.succ_pos _
    · have := hsort.1 a ha; omega
    · have hnea : x ≠ a := by have := hsort.1 a ha; omega
      have hneb : x ≠ b := by have := hsort.1 b hb; omega
      rw [List.idxOf_cons_ne _ (by simp [hnea]), List.idxOf_cons_ne _ (by simp [hneb])]
      exact Nat.succ_lt_succ (ih hsort.2 ha hb)

lemma idxOf_getElem_of_nodup {l : List ℕ} (hnodup : l.Nodup) (j : ℕ) (hj : j < l.length) :
    l.idxOf l[j] = j := by
  induction l generalizing j with
  | nil => cases hj
  | cons x xs ih =>
    rw [List.nodup_cons] at hnodup
    cases j with
    | zero => simp
    | succ j' =>
      simp only [List.getElem_cons_succ]
      have hj' : j' < xs.length := by simp only [List.length_cons] at hj; omega
      have hne : x ≠ xs[j'] := fun h => hnodup.1 (h ▸ List.getElem_mem hj')
      rw [List.idxOf_cons_ne _ (by simp [hne]), ih hnodup.2 j' hj']

lemma lamGates_isAO2 {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (lamList : List ℕ) (hsort : lamList.Pairwise (· < ·))
    (hmem_lt : ∀ k ∈ lamList, k < C.gates.length) :
    IsAO2 n ⟨lamGates n C lamList, 0⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [lamGates, List.mem_map] at hg
    rcases hg with ⟨k, _, rfl⟩
    exact Or.inr rfl
  · intro j hj u hu
    simp only [lamGates, List.length_map] at hj
    rw [gateAt_eq (by simp [lamGates, hj])] at hu
    simp only [lamGates, List.getElem_map, List.mem_cons, List.not_mem_nil, or_false] at hu
    set k := lamList[j]
    have hk_mem : k ∈ lamList := List.getElem_mem hj
    have hk_lt : k < C.gates.length := hmem_lt k hk_mem
    have hidx : lamList.idxOf k = j := by
      have hnodup : lamList.Nodup := hsort.imp (fun {a b} h => Nat.ne_of_lt h)
      exact idxOf_getElem_of_nodup hnodup j hj
    have check_b : ∀ b : Fin 2, bypass n C lamList (opnd C k b) < n + j := by
      intro b
      have hltb : opnd C k b < n + k := opnd_lt hAO hk_lt b
      rcases bypass_bound hAO lamList hsort (opnd C k b) (by omega) with hlt | ⟨hnle, k', hk'm, hk'le, heq⟩
      · omega
      · rw [heq]
        have hk'lt : k' < k := by omega
        have hlt_idx := idxOf_lt_of_pairwise_lt hsort hk'm hk_mem hk'lt
        rw [hidx] at hlt_idx
        omega
    rcases hu with rfl | rfl
    · exact check_b 0
    · exact check_b 1
  · intro g hg
    simp only [lamGates, List.mem_map] at hg
    rcases hg with ⟨k, _, rfl⟩
    rfl

-- Leaf-side property for wires evaluated through lamGates
def LeafWire {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (w : ℕ) : Prop :=
  w < n + C.gates.length ∧ (orIn n C w).Nonempty ∧
    (∀ k, w = n + k → ¬ BelowF G C k) ∧
    (∀ k, OrReaches n C w k → k ∈ orN G C →
      (orIn n C (opnd C k 0)).Nonempty → (orIn n C (opnd C k 1)).Nonempty → k ∈ lam G C)

lemma leafWire_opnd {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hLift : IsLiftFixedPoint G C) (hne : ∃ u v : Fin n, G.Adj u v)
    {k : ℕ} (hk : k ∈ orN G C) (hlw : LeafWire G C (n + k))
    (b : Fin 2) (hneb : (orIn n C (opnd C k b)).Nonempty) :
    LeafWire G C (opnd C k b) := by
  have hk' := mem_orN_iff.mp hk
  have hlt : opnd C k b < n + k := opnd_lt hL.1 hk'.1 b
  refine ⟨by omega, hneb, ?_, ?_⟩
  · intro m hm hbm
    exact lift_no_belowF_orN_opnd hL hLift hne hk'.1 hk'.2.1 hk'.2.2 b (by rw [hm]; exact hbm)
  · intro m hrm hm_orN h0 h1
    apply hlw.2.2.2 m _ hm_orN h0 h1
    exact (orReaches_gate_iff hk'.1).mpr
      (Or.inr ⟨hk'.2.1, opnd C k b, opnd_mem hL.1 hk'.1 b, hrm.1, hlt, hrm⟩)

lemma leafWire_of_top_side {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hne : ∃ u v : Fin n, G.Adj u v)
    {a : ℕ} (ha : a ∈ tops G C) (b : Fin 2)
    (hneb : (side (n := n) C a b).Nonempty) (hcard : (side (n := n) C a (1 - b)).card = 1) :
    LeafWire G C (opnd C a b) := by
  have ha' := mem_tops_iff.mp ha
  have hlt : opnd C a b < n + a := opnd_lt hL.1 ha'.1 b
  refine ⟨by omega, hneb, ?_, ?_⟩
  · intro m hm hbm
    exact least_no_belowF_and_opnd hL hne ha'.1 ha'.2.1 b (by rw [hm]; exact hbm)
  · intro m hrm hm_orN h0 h1
    unfold lam
    exact Finset.mem_filter.mpr ⟨hm_orN, h0, h1, a, ha, b, hcard, hrm⟩

lemma bypass_wval {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hLift : IsLiftFixedPoint G C) (hne : ∃ u v : Fin n, G.Adj u v)
    (lamList : List ℕ) (hsort : lamList.Pairwise (· < ·))
    (hlam_iff : ∀ k, k ∈ lamList ↔ k ∈ lam G C)
    (x : Fin n → Bool) :
    ∀ w, LeafWire G C w →
      bypass n C lamList w < n + lamList.length ∧
      wval ⟨lamGates n C lamList, 0⟩ x (bypass n C lamList w) =
        decide (∃ u ∈ orIn n C w, x u = true) := by
  have hmem_lt : ∀ k ∈ lamList, k < C.gates.length := fun k hk => by
    have := (hlam_iff k).mp hk; exact (mem_orN_iff.mp (Finset.mem_filter.mp this).1).1
  have hAO_lam := lamGates_isAO2 hL.1 lamList hsort hmem_lt
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hlw
    by_cases hwn : w < n
    · have hbp : bypass n C lamList w = w := by unfold bypass; rw [dif_pos hwn]
      rw [hbp]
      refine ⟨by omega, ?_⟩
      rw [wval_input _ x w hwn]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      constructor
      · intro h; exact ⟨⟨w, hwn⟩, (mem_orIn_input C _ _).mpr rfl, h⟩
      · rintro ⟨u, hu, hxu⟩
        have heq := (mem_orIn_input C u ⟨w, hwn⟩).mp hu
        subst heq; exact hxu
    · have hk_lt : w - n < C.gates.length := by have := hlw.1; omega
      have hw_eq : w = n + (w - n) := by omega
      set k := w - n
      have hnbk : ¬ BelowF G C k := hlw.2.2.1 k hw_eq
      have hork : (gateAt C k).op = GateOp.or := by
        rcases hL.1.1 _ (gateAt_mem hk_lt) with hand | hor
        · exfalso
          have hemp := orIn_and_eq_empty (n := n) hk_lt hand
          rw [← hw_eq] at hemp
          exact hlw.2.1.ne_empty hemp
        · exact hor
      have hk_orN : k ∈ orN G C := mem_orN_iff.mpr ⟨hk_lt, hork, hnbk⟩
      have hlw_k : LeafWire G C (n + k) := by rwa [← hw_eq]
      have horIn_eq : orIn n C w = orIn n C (opnd C k 0) ∪ orIn n C (opnd C k 1) := by
        rw [hw_eq]; exact orIn_or_eq_union hL.1 hk_lt hork
      have hlt0 : opnd C k 0 < w := by have := opnd_lt hL.1 hk_lt 0; omega
      have hlt1 : opnd C k 1 < w := by have := opnd_lt hL.1 hk_lt 1; omega
      by_cases hmem : k ∈ lamList
      · have hbp : bypass n C lamList w = n + lamList.idxOf k := by
          unfold bypass; rw [dif_neg hwn, dif_pos hk_lt, if_pos hmem]
        have hidx_lt : lamList.idxOf k < lamList.length := List.idxOf_lt_length_iff.mpr hmem
        have hkl : k ∈ lam G C := (hlam_iff k).mp hmem
        have h0ne : (orIn n C (opnd C k 0)).Nonempty := (Finset.mem_filter.mp hkl).2.1
        have h1ne : (orIn n C (opnd C k 1)).Nonempty := (Finset.mem_filter.mp hkl).2.2.1
        have ih0 := ih (opnd C k 0) hlt0 (leafWire_opnd hL hLift hne hk_orN hlw_k 0 h0ne)
        have ih1 := ih (opnd C k 1) hlt1 (leafWire_opnd hL hLift hne hk_orN hlw_k 1 h1ne)
        rw [hbp]
        refine ⟨by omega, ?_⟩
        have hj' : lamList.idxOf k < (lamGates n C lamList).length := by simp [lamGates, hidx_lt]
        have hget : lamList[lamList.idxOf k] = k := List.getElem_idxOf hidx_lt
        have hgat : gateAt ⟨lamGates n C lamList, 0⟩ (lamList.idxOf k) =
            ⟨GateOp.or, [bypass n C lamList (opnd C k 0), bypass n C lamList (opnd C k 1)]⟩ := by
          rw [gateAt_eq hj']; simp [lamGates, hget]
        rw [wval_gate_or hAO_lam x hj' (by rw [hgat])]
        have hop0 : opnd ⟨lamGates n C lamList, 0⟩ (lamList.idxOf k) 0 =
            bypass n C lamList (opnd C k 0) := by unfold opnd; rw [hgat]; rfl
        have hop1 : opnd ⟨lamGates n C lamList, 0⟩ (lamList.idxOf k) 1 =
            bypass n C lamList (opnd C k 1) := by unfold opnd; rw [hgat]; rfl
        rw [hop0, hop1, ih0.2, ih1.2, horIn_eq]
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.or_eq_true, decide_eq_true_eq, Finset.mem_union]
        constructor
        · rintro (⟨u, hu, hxu⟩ | ⟨u, hu, hxu⟩)
          · exact ⟨u, Or.inl hu, hxu⟩
          · exact ⟨u, Or.inr hu, hxu⟩
        · rintro ⟨u, hu | hu, hxu⟩
          · exact Or.inl ⟨u, hu, hxu⟩
          · exact Or.inr ⟨u, hu, hxu⟩
      · have hnotboth : ¬ ((orIn n C (opnd C k 0)).Nonempty ∧ (orIn n C (opnd C k 1)).Nonempty) := by
          rintro ⟨h0, h1⟩
          apply hmem
          rw [hlam_iff]
          exact hlw_k.2.2.2 k (orReaches_self hk_lt) hk_orN h0 h1
        by_cases h0ne : (orIn n C (opnd C k 0)).Nonempty
        · have h1emp : orIn n C (opnd C k 1) = ∅ := by
            by_contra hne1; exact hnotboth ⟨h0ne, Finset.nonempty_iff_ne_empty.mpr hne1⟩
          have hbp : bypass n C lamList w = bypass n C lamList (opnd C k 0) := by
            conv_lhs => unfold bypass
            dsimp only
            rw [dif_neg hwn, dif_pos hk_lt, if_neg hmem, if_pos h0ne, dif_pos hlt0]
          rw [hbp, horIn_eq, h1emp, Finset.union_empty]
          exact ih (opnd C k 0) hlt0 (leafWire_opnd hL hLift hne hk_orN hlw_k 0 h0ne)
        · have h0emp : orIn n C (opnd C k 0) = ∅ := Finset.not_nonempty_iff_eq_empty.mp h0ne
          have h1ne : (orIn n C (opnd C k 1)).Nonempty := by
            have hne' := hlw.2.1
            rw [horIn_eq, h0emp, Finset.empty_union] at hne'
            exact hne'
          have hbp : bypass n C lamList w = bypass n C lamList (opnd C k 1) := by
            conv_lhs => unfold bypass
            dsimp only
            rw [dif_neg hwn, dif_pos hk_lt, if_neg hmem, if_neg h0ne, dif_pos hlt1]
          rw [hbp, horIn_eq, h0emp, Finset.empty_union]
          exact ih (opnd C k 1) hlt1 (leafWire_opnd hL hLift hne hk_orN hlw_k 1 h1ne)

-- Folding Layer 2 + Layer 3 cleanly:
-- Given a list of stars: each item is (v : Fin n, baseWire : Option ℕ, extraVerts : List (Fin n))
-- If baseWire = some bw and extraVerts = []: appends 1 AND gate (v, bw), cost = 1.
-- If baseWire = some bw and extraVerts ≠ []: builds OR of extraVerts (len - 1), OR with bw (1), AND with v (1), cost = extraVerts.length + 1.
-- If baseWire = none and extraVerts ≠ []: builds OR of extraVerts (len - 1), AND with v (1), cost = extraVerts.length.

def addStar (n : ℕ) (gs : List Gate) (v : Fin n) (base : Option ℕ) (extra : List (Fin n)) :
    List Gate × ℕ :=
  match base, extra with
  | some bw, [] =>
    (gs ++ [⟨GateOp.and, [v.val, bw]⟩], n + gs.length)
  | some bw, e :: es =>
    let r1 := appendOrList n gs ((e :: es).map Fin.val)
    let gs2 := r1.1 ++ [⟨GateOp.or, [bw, r1.2]⟩]
    (gs2 ++ [⟨GateOp.and, [v.val, n + r1.1.length]⟩], n + gs2.length)
  | none, e :: es =>
    let r1 := appendOrList n gs ((e :: es).map Fin.val)
    (r1.1 ++ [⟨GateOp.and, [v.val, r1.2]⟩], n + r1.1.length)
  | none, [] => (gs, 0)

def addStars (n : ℕ) (gs : List Gate) :
    List (Fin n × Option ℕ × List (Fin n)) → List Gate × List ℕ
  | [] => (gs, [])
  | (v, base, extra) :: rest =>
    let r := addStar n gs v base extra
    let r2 := addStars n r.1 rest
    (r2.1, r.2 :: r2.2)

lemma addStar_spec {n : ℕ} {gs : List Gate} (hAO : IsAO2 n ⟨gs, 0⟩)
    (v : Fin n) (base : Option ℕ) (extra : List (Fin n))
    (hbase : ∀ bw, base = some bw → bw < n + gs.length)
    (hne : base.isSome ∨ extra ≠ []) :
    (∃ ex : List Gate, (addStar n gs v base extra).1 = gs ++ ex) ∧
    (addStar n gs v base extra).1.length =
      gs.length + extra.length + (if base.isSome then 1 else 0) ∧
    IsAO2 n ⟨(addStar n gs v base extra).1, 0⟩ ∧
    (addStar n gs v base extra).2 < n + (addStar n gs v base extra).1.length ∧
    ∀ x : Fin n → Bool,
      wval ⟨(addStar n gs v base extra).1, 0⟩ x (addStar n gs v base extra).2 =
        (x v && (decide (∃ bw, base = some bw ∧ wval ⟨gs, 0⟩ x bw = true) ||
          decide (∃ u ∈ extra, x u = true))) := by
  cases base with
  | none =>
    cases extra with
    | nil => simp at hne
    | cons e es =>
      have hws : ∀ w ∈ (e :: es).map Fin.val, w < n + gs.length := by
        intro w hw; simp only [List.mem_map] at hw; rcases hw with ⟨u, _, rfl⟩; omega
      obtain ⟨ex1, hex1⟩ := appendOrList_prefix n gs ((e :: es).map Fin.val)
      have hlen1 := appendOrList_len n gs ((e :: es).map Fin.val) (by simp)
      have ⟨hAO1, hlt1⟩ := appendOrList_isAO2 hAO ((e :: es).map Fin.val) (by simp) hws
      dsimp only [addStar]
      set gs1 := (appendOrList n gs ((e :: es).map Fin.val)).1
      set w1 := (appendOrList n gs ((e :: es).map Fin.val)).2
      have hAO2 := appendGate_isAO2 hAO1 (Or.inl rfl) (by omega : v.val < n + gs1.length) hlt1
      refine ⟨⟨ex1 ++ [⟨GateOp.and, [v.val, w1]⟩], by rw [hex1, List.append_assoc]⟩,
        ?_, hAO2, by simp, ?_⟩
      · simp only [List.length_append, List.length_cons, List.length_nil, hlen1, List.length_map,
          Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
        omega
      · intro x
        have hgat : gateAt ⟨gs1 ++ [⟨GateOp.and, [v.val, w1]⟩], 0⟩ gs1.length =
            ⟨GateOp.and, [v.val, w1]⟩ := by rw [gateAt_eq (by simp)]; simp
        rw [wval_gate_and hAO2 x (by simp) (by rw [hgat])]
        have hop0 : opnd ⟨gs1 ++ [⟨GateOp.and, [v.val, w1]⟩], 0⟩ gs1.length 0 = v.val := by
          unfold opnd; rw [hgat]; rfl
        have hop1 : opnd ⟨gs1 ++ [⟨GateOp.and, [v.val, w1]⟩], 0⟩ gs1.length 1 = w1 := by
          unfold opnd; rw [hgat]; rfl
        rw [hop0, hop1, wval_input _ x v.val v.isLt,
          wval_append_lt gs1 [⟨GateOp.and, [v.val, w1]⟩] 0 0 x hlt1,
          appendOrList_wval hAO x ((e :: es).map Fin.val) (by simp) hws]
        congr 1
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.or_eq_true, decide_eq_true_eq, List.mem_map, false_or, reduceCtorEq, false_and, exists_false]
        constructor
        · rintro ⟨_, ⟨u, hu, rfl⟩, hxu⟩
          rw [wval_input _ x u.val u.isLt] at hxu; exact ⟨u, hu, hxu⟩
        · rintro ⟨u, hu, hxu⟩
          exact ⟨u.val, ⟨u, hu, rfl⟩, by rw [wval_input _ x u.val u.isLt]; exact hxu⟩
  | some bw =>
    have hbw : bw < n + gs.length := hbase bw rfl
    cases extra with
    | nil =>
      have hAO2 := appendGate_isAO2 hAO (Or.inl rfl) (by omega : v.val < n + gs.length) hbw
      refine ⟨⟨[⟨GateOp.and, [v.val, bw]⟩], rfl⟩, ?_, hAO2, by simp [addStar], ?_⟩
      · simp [addStar]
      · intro x
        simp only [addStar]
        have hgat : gateAt ⟨gs ++ [⟨GateOp.and, [v.val, bw]⟩], 0⟩ gs.length =
            ⟨GateOp.and, [v.val, bw]⟩ := by rw [gateAt_eq (by simp)]; simp
        rw [wval_gate_and hAO2 x (by simp) (by rw [hgat])]
        have hop0 : opnd ⟨gs ++ [⟨GateOp.and, [v.val, bw]⟩], 0⟩ gs.length 0 = v.val := by
          unfold opnd; rw [hgat]; rfl
        have hop1 : opnd ⟨gs ++ [⟨GateOp.and, [v.val, bw]⟩], 0⟩ gs.length 1 = bw := by
          unfold opnd; rw [hgat]; rfl
        rw [hop0, hop1, wval_input _ x v.val v.isLt,
          wval_append_lt gs [⟨GateOp.and, [v.val, bw]⟩] 0 0 x hbw]
        congr 1
        cases h : wval ⟨gs, 0⟩ x bw <;> simp [h]
    | cons e es =>
      have hws : ∀ w ∈ (e :: es).map Fin.val, w < n + gs.length := by
        intro w hw; simp only [List.mem_map] at hw; rcases hw with ⟨u, _, rfl⟩; omega
      obtain ⟨ex1, hex1⟩ := appendOrList_prefix n gs ((e :: es).map Fin.val)
      have hlen1 := appendOrList_len n gs ((e :: es).map Fin.val) (by simp)
      have ⟨hAO1, hlt1⟩ := appendOrList_isAO2 hAO ((e :: es).map Fin.val) (by simp) hws
      dsimp only [addStar]
      set gs1 := (appendOrList n gs ((e :: es).map Fin.val)).1
      set w1 := (appendOrList n gs ((e :: es).map Fin.val)).2
      have hbw1 : bw < n + gs1.length := by rw [hex1, List.length_append]; omega
      have hAO2 := appendGate_isAO2 hAO1 (Or.inr rfl) hbw1 hlt1
      set gs2 := gs1 ++ [⟨GateOp.or, [bw, w1]⟩]
      have hAO3 := appendGate_isAO2 hAO2 (Or.inl rfl)
        (by simp [gs2]; omega : v.val < n + gs2.length) (by simp [gs2] : n + gs1.length < n + gs2.length)
      refine ⟨⟨ex1 ++ [⟨GateOp.or, [bw, w1]⟩, ⟨GateOp.and, [v.val, n + gs1.length]⟩],
          by simp only [gs2, hex1, List.append_assoc]; rfl⟩,
        ?_, hAO3, by simp [gs2], ?_⟩
      · simp only [gs2, List.length_append, List.length_cons, List.length_nil, hlen1,
          List.length_map, Option.isSome_some, ↓reduceIte]
        omega
      · intro x
        have hgat3 : gateAt ⟨gs2 ++ [⟨GateOp.and, [v.val, n + gs1.length]⟩], 0⟩ gs2.length =
            ⟨GateOp.and, [v.val, n + gs1.length]⟩ := by rw [gateAt_eq (by simp)]; simp
        rw [wval_gate_and hAO3 x (by simp) (by rw [hgat3])]
        have hop30 : opnd ⟨gs2 ++ [⟨GateOp.and, [v.val, n + gs1.length]⟩], 0⟩ gs2.length 0 = v.val := by
          unfold opnd; rw [hgat3]; rfl
        have hop31 : opnd ⟨gs2 ++ [⟨GateOp.and, [v.val, n + gs1.length]⟩], 0⟩ gs2.length 1 =
            n + gs1.length := by unfold opnd; rw [hgat3]; rfl
        rw [hop30, hop31, wval_input _ x v.val v.isLt,
          wval_append_lt gs2 [⟨GateOp.and, [v.val, n + gs1.length]⟩] 0 0 x (by simp [gs2])]
        have hgat2 : gateAt ⟨gs2, 0⟩ gs1.length = ⟨GateOp.or, [bw, w1]⟩ := by
          rw [gateAt_eq (by simp [gs2])]; simp [gs2]
        rw [wval_gate_or hAO2 x (by simp [gs2]) (by rw [hgat2])]
        have hop20 : opnd ⟨gs2, 0⟩ gs1.length 0 = bw := by unfold opnd; rw [hgat2]; rfl
        have hop21 : opnd ⟨gs2, 0⟩ gs1.length 1 = w1 := by unfold opnd; rw [hgat2]; rfl
        rw [hop20, hop21, wval_append_lt gs1 [⟨GateOp.or, [bw, w1]⟩] 0 0 x hbw1,
          wval_append_lt gs1 [⟨GateOp.or, [bw, w1]⟩] 0 0 x hlt1]
        have hvbw : wval ⟨gs1, 0⟩ x bw = wval ⟨gs, 0⟩ x bw := by
          rw [hex1]; exact wval_append_lt gs ex1 0 0 x hbw
        rw [hvbw, appendOrList_wval hAO x ((e :: es).map Fin.val) (by simp) hws]
        congr 1
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.or_eq_true, decide_eq_true_eq, List.mem_map, Option.some.injEq, exists_eq_left']
        constructor
        · rintro (h | ⟨_, ⟨u, hu, rfl⟩, hxu⟩)
          · exact Or.inl h
          · rw [wval_input _ x u.val u.isLt] at hxu; exact Or.inr ⟨u, hu, hxu⟩
        · rintro (h | ⟨u, hu, hxu⟩)
          · exact Or.inl h
          · exact Or.inr ⟨u.val, ⟨u, hu, rfl⟩, by rw [wval_input _ x u.val u.isLt]; exact hxu⟩

lemma addStars_spec {n : ℕ} {gs : List Gate} (hAO : IsAO2 n ⟨gs, 0⟩)
    (items : List (Fin n × Option ℕ × List (Fin n)))
    (hitems : ∀ it ∈ items, (∀ bw, it.2.1 = some bw → bw < n + gs.length) ∧
      (it.2.1.isSome ∨ it.2.2 ≠ [])) :
    (∃ ex : List Gate, (addStars n gs items).1 = gs ++ ex) ∧
    (addStars n gs items).1.length =
      gs.length + (items.map fun it => it.2.2.length + (if it.2.1.isSome then 1 else 0)).sum ∧
    (addStars n gs items).2.length = items.length ∧
    IsAO2 n ⟨(addStars n gs items).1, 0⟩ ∧
    (∀ w ∈ (addStars n gs items).2, w < n + (addStars n gs items).1.length) ∧
    ∀ x : Fin n → Bool,
      (∃ w ∈ (addStars n gs items).2, wval ⟨(addStars n gs items).1, 0⟩ x w = true) ↔
        ∃ it ∈ items, x it.1 = true ∧
          ((∃ bw, it.2.1 = some bw ∧ wval ⟨gs, 0⟩ x bw = true) ∨
            ∃ u ∈ it.2.2, x u = true) := by
  induction items generalizing gs with
  | nil =>
    refine ⟨⟨[], by simp [addStars]⟩, by simp [addStars], rfl, hAO, by simp [addStars], ?_⟩
    intro x; simp [addStars]
  | cons it rest ih =>
    rcases it with ⟨v, base, extra⟩
    have hit := hitems (v, base, extra) (by simp)
    obtain ⟨⟨ex1, hex1⟩, hlen1, hAO1, hlt1, hval1⟩ := addStar_spec hAO v base extra hit.1 hit.2
    dsimp only [addStars]
    set r := addStar n gs v base extra
    have hrest : ∀ it' ∈ rest, (∀ bw, it'.2.1 = some bw → bw < n + r.1.length) ∧
        (it'.2.1.isSome ∨ it'.2.2 ≠ []) := by
      intro it' hit'
      have h0 := hitems it' (by simp [hit'])
      exact ⟨fun bw hbw => by have := h0.1 bw hbw; rw [hex1, List.length_append]; omega, h0.2⟩
    obtain ⟨⟨ex2, hex2⟩, hlen2, hwlen2, hAO2, hlt2, hval2⟩ := ih hAO1 hrest
    refine ⟨⟨ex1 ++ ex2, by rw [hex2, hex1, List.append_assoc]⟩, ?_, ?_, hAO2, ?_, ?_⟩
    · simp only [hlen2, hlen1, List.map_cons, List.sum_cons]; omega
    · simp only [List.length_cons, hwlen2]
    · intro w hw
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · rw [hex2, List.length_append]; omega
      · exact hlt2 w hw
    · intro x
      simp only [List.mem_cons, exists_eq_or_imp]
      have hvw : wval ⟨(addStars n r.1 rest).1, 0⟩ x r.2 =
          (x v && (decide (∃ bw, base = some bw ∧ wval ⟨gs, 0⟩ x bw = true) ||
            decide (∃ u ∈ extra, x u = true))) := by
        rw [hex2, wval_append_lt r.1 ex2 0 0 x hlt1, hval1 x]
      have hiff_rest : (∃ w ∈ (addStars n r.1 rest).2, wval ⟨(addStars n r.1 rest).1, 0⟩ x w = true) ↔
          ∃ it' ∈ rest, x it'.1 = true ∧
            ((∃ bw, it'.2.1 = some bw ∧ wval ⟨gs, 0⟩ x bw = true) ∨
              ∃ u ∈ it'.2.2, x u = true) := by
        rw [hval2 x]
        apply exists_congr; intro it'
        apply and_congr_right; intro hit'
        apply and_congr_right; intro _
        apply or_congr_left
        apply exists_congr; intro bw
        apply and_congr_right; intro hbw
        have hlt_bw := (hitems it' (by simp [hit'])).1 bw hbw
        rw [hex1, wval_append_lt gs ex1 0 0 x hlt_bw]
      rw [hvw, hiff_rest]
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]

-- Master size reduction lemma: if we can cover Ustar with (Zact, L, Zhas, topOf),
-- then 2 * |centreless| + |orN \ lam| + 2 <= sum_{v in Zact} |L v| + |Zact \ Zhas|.

lemma master_surgery_bound {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hLift : IsLiftFixedPoint G C) (h4 : NoFourCycle G)
    {g1 g2 : ℕ} (hg12 : g1 ≠ g2) (hjunk : ∀ k, k ∈ junk G C ↔ k = g1 ∨ k = g2)
    (hne : ∃ u v : Fin n, G.Adj u v)
    (Zact Zhas : Finset (Fin n)) (L : Fin n → Finset (Fin n)) (topOf : Fin n → ℕ)
    (hZsub : Zhas ⊆ Zact)
    (hLne : ∀ v ∈ Zact, (L v).Nonempty)
    (hLadj : ∀ v ∈ Zact, ∀ u ∈ L v, G.Adj v u)
    (hUcov : ∀ e ∈ Ustar G C, ∃ v ∈ Zact, ∃ u ∈ L v, e = s(v, u))
    (htop_mem : ∀ v ∈ Zhas, topOf v ∈ tops G C \ centreless G C)
    (htop_side : ∀ v ∈ Zhas, side (n := n) C (topOf v) 0 = {v} ∨ side (n := n) C (topOf v) 1 = {v})
    (htop_inj : ∀ v1 ∈ Zhas, ∀ v2 ∈ Zhas, topOf v1 = topOf v2 → v1 = v2) :
    2 * (centreless G C).card + (orN G C \ lam G C).card + 2 ≤
      (∑ v ∈ Zact, (L v).card) + (Zact \ Zhas).card := by
  classical
  set S_tops := tops G C \ centreless G C
  set lamList := (lam G C).sort (· ≤ ·)
  have hsort : lamList.Pairwise (· < ·) :=
    ((Finset.pairwise_sort (lam G C) (· ≤ ·)).and (Finset.sort_nodup (lam G C) (· ≤ ·))).imp
      (fun ⟨h1, h2⟩ => Nat.lt_of_le_of_ne h1 h2)
  have hlam_iff : ∀ k, k ∈ lamList ↔ k ∈ lam G C := fun k => Finset.mem_sort (· ≤ ·)
  have hlam_len : lamList.length = (lam G C).card := Finset.length_sort (· ≤ ·)
  have hmem_lt : ∀ k ∈ lamList, k < C.gates.length := fun k hk =>
    (mem_orN_iff.mp (Finset.mem_filter.mp ((hlam_iff k).mp hk)).1).1
  set gs1 := lamGates n C lamList
  have hAO1 : IsAO2 n ⟨gs1, 0⟩ := lamGates_isAO2 hL.1 lamList hsort hmem_lt
  have hgs1_len : gs1.length = (lam G C).card := by simp [gs1, lamGates, hlam_len]
  -- Choose center and leaf side for every a in S_tops:
  -- if a = topOf v for some v in Zhas, choose that v and extra = (L v).toList;
  -- else choose an arbitrary center of a and extra = [].
  let mkTopItem : ℕ → Fin n × Option ℕ × List (Fin n) := fun a =>
    if h : ∃ v ∈ Zhas, topOf v = a then
      let v := Classical.choose h
      have hv := Classical.choose_spec h
      have hs : side (n := n) C a 0 = {v} ∨ side (n := n) C a 1 = {v} := by
        rw [← hv.2]; exact htop_side v hv.1
      let b : Fin 2 := if side (n := n) C a 0 = {v} then 1 else 0
      (v, some (bypass n C lamList (opnd C a b)), (L v).toList)
    else
      if ha : a ∈ S_tops then
        have hst := top_is_star hL.1 h4 ha
        if h0 : (side (n := n) C a 0).card = 1 then
          let v := Classical.choose (Finset.card_eq_one.mp h0)
          (v, some (bypass n C lamList (opnd C a 1)), [])
        else
          have h1 : (side (n := n) C a 1).card = 1 := hst.2.2.resolve_left h0
          let v := Classical.choose (Finset.card_eq_one.mp h1)
          (v, some (bypass n C lamList (opnd C a 0)), [])
      else
        (Classical.choose hne, none, [])
  let topItems := S_tops.toList.map mkTopItem
  let newItems := (Zact \ Zhas).toList.map fun v => (v, (none : Option ℕ), (L v).toList)
  let allItems := topItems ++ newItems
  -- Helper: check mkTopItem properties for a in S_tops
  have htopItem_ok : ∀ a ∈ S_tops,
      let it := mkTopItem a
      (∀ bw, it.2.1 = some bw → bw < n + gs1.length) ∧
      it.2.1.isSome ∧
      (∀ x : Fin n → Bool,
        (x it.1 = true ∧ ((∃ bw, it.2.1 = some bw ∧ wval ⟨gs1, 0⟩ x bw = true) ∨
          ∃ u ∈ it.2.2, x u = true)) ↔
        ((∃ u ∈ side (n := n) C a 0, x u = true) ∧ (∃ v ∈ side (n := n) C a 1, x v = true)) ∨
          ∃ v ∈ Zhas, topOf v = a ∧ x v = true ∧ ∃ u ∈ L v, x u = true) := by
    intro a ha
    have ha_top : a ∈ tops G C := (Finset.mem_sdiff.mp ha).1
    have hst := top_is_star hL.1 h4 ha
    by_cases h : ∃ v ∈ Zhas, topOf v = a
    · simp only [mkTopItem, dif_pos h]
      set v := Classical.choose h
      have hv := Classical.choose_spec h
      have hs : side (n := n) C a 0 = {v} ∨ side (n := n) C a 1 = {v} := by
        rw [← hv.2]; exact htop_side v hv.1
      set b : Fin 2 := if side (n := n) C a 0 = {v} then 1 else 0
      have h1mb : side (n := n) C a (1 - b) = {v} := by
        by_cases h0 : side (n := n) C a 0 = {v}
        · simp [b, h0]
        · simp [b, h0]; exact hs.resolve_left h0
      have hcard : (side (n := n) C a (1 - b)).card = 1 := by rw [h1mb]; simp
      have hneb : (side (n := n) C a b).Nonempty := by
        by_cases h0 : side (n := n) C a 0 = {v}
        · simp [b, h0]; exact hst.2.1
        · simp [b, h0]; exact hst.1
      have hlw := leafWire_of_top_side hL hne ha_top b hneb hcard
      refine ⟨?_, rfl, ?_⟩
      · intro bw hbw
        injection hbw with hbw; subst hbw
        have := (bypass_wval hL hLift hne lamList hsort hlam_iff (fun _ => false) _ hlw).1
        rw [hgs1_len, ← hlam_len]; exact this
      · intro x
        have hbp : wval ⟨gs1, 0⟩ x (bypass n C lamList (opnd C a b)) =
            decide (∃ u ∈ orIn n C (opnd C a b), x u = true) :=
          (bypass_wval hL hLift hne lamList hsort hlam_iff x _ hlw).2
        simp only [Option.some.injEq, exists_eq_left', hbp, decide_eq_true_eq, Finset.mem_toList]
        have huniq : ∀ v' ∈ Zhas, topOf v' = a → v' = v := fun v' hv' heq =>
          htop_inj v' hv' v hv.1 (heq.trans hv.2.symm)
        constructor
        · rintro ⟨hxv, hleaf | ⟨u, hu, hxu⟩⟩
          · left
            by_cases h0 : side (n := n) C a 0 = {v}
            · simp only [b, if_pos h0] at hleaf
              exact ⟨⟨v, by rw [h0]; simp, hxv⟩, hleaf⟩
            · simp only [b, if_neg h0] at hleaf
              have h1 : side (n := n) C a 1 = {v} := hs.resolve_left h0
              exact ⟨hleaf, ⟨v, by rw [h1]; simp, hxv⟩⟩
          · right; exact ⟨v, hv.1, hv.2, hxv, u, hu, hxu⟩
        · rintro (⟨h0, h1⟩ | ⟨v', hv', heq, hxv', u, hu, hxu⟩)
          · by_cases hs0 : side (n := n) C a 0 = {v}
            · simp only [b, if_pos hs0]
              rcases h0 with ⟨u0, hu0, hxu0⟩
              rw [hs0, Finset.mem_singleton] at hu0; subst hu0
              exact ⟨hxu0, Or.inl h1⟩
            · simp only [b, if_neg hs0]
              have hs1 : side (n := n) C a 1 = {v} := hs.resolve_left hs0
              rcases h1 with ⟨u1, hu1, hxu1⟩
              rw [hs1, Finset.mem_singleton] at hu1; subst hu1
              exact ⟨hxu1, Or.inl h0⟩
          · have hv'eq := huniq v' hv' heq; subst hv'eq
            exact ⟨hxv', Or.inr ⟨u, hu, hxu⟩⟩
    · simp only [mkTopItem, dif_neg h, dif_pos ha]
      by_cases h0 : (side (n := n) C a 0).card = 1
      · simp only [dif_pos h0]
        set v := Classical.choose (Finset.card_eq_one.mp h0)
        have hv : side (n := n) C a 0 = {v} := Classical.choose_spec (Finset.card_eq_one.mp h0)
        have hlw := leafWire_of_top_side hL hne ha_top 1 hst.2.1 (by simpa using h0)
        refine ⟨?_, rfl, ?_⟩
        · intro bw hbw
          injection hbw with hbw; subst hbw
          have := (bypass_wval hL hLift hne lamList hsort hlam_iff (fun _ => false) _ hlw).1
          rw [hgs1_len, ← hlam_len]; exact this
        · intro x
          have hbp : wval ⟨gs1, 0⟩ x (bypass n C lamList (opnd C a 1)) =
              decide (∃ u ∈ orIn n C (opnd C a 1), x u = true) :=
            (bypass_wval hL hLift hne lamList hsort hlam_iff x _ hlw).2
          simp only [Option.some.injEq, exists_eq_left', hbp, decide_eq_true_eq,
            List.not_mem_nil, false_and, exists_false, or_false]
          have hno : ¬ ∃ v' ∈ Zhas, topOf v' = a ∧ x v' = true ∧ ∃ u ∈ L v', x u = true := by
            rintro ⟨v', hv', heq, _⟩; exact h ⟨v', hv', heq⟩
          rw [or_iff_left hno, hv]
          simp only [Finset.mem_singleton, exists_eq_left]
          rfl
      · simp only [dif_neg h0]
        have h1 : (side (n := n) C a 1).card = 1 := hst.2.2.resolve_left h0
        set v := Classical.choose (Finset.card_eq_one.mp h1)
        have hv : side (n := n) C a 1 = {v} := Classical.choose_spec (Finset.card_eq_one.mp h1)
        have hlw := leafWire_of_top_side hL hne ha_top 0 hst.1 (by simpa using h1)
        refine ⟨?_, rfl, ?_⟩
        · intro bw hbw
          injection hbw with hbw; subst hbw
          have := (bypass_wval hL hLift hne lamList hsort hlam_iff (fun _ => false) _ hlw).1
          rw [hgs1_len, ← hlam_len]; exact this
        · intro x
          have hbp : wval ⟨gs1, 0⟩ x (bypass n C lamList (opnd C a 0)) =
              decide (∃ u ∈ orIn n C (opnd C a 0), x u = true) :=
            (bypass_wval hL hLift hne lamList hsort hlam_iff x _ hlw).2
          simp only [Option.some.injEq, exists_eq_left', hbp, decide_eq_true_eq,
            List.not_mem_nil, false_and, exists_false, or_false]
          have hno : ¬ ∃ v' ∈ Zhas, topOf v' = a ∧ x v' = true ∧ ∃ u ∈ L v', x u = true := by
            rintro ⟨v', hv', heq, _⟩; exact h ⟨v', hv', heq⟩
          rw [or_iff_left hno, hv]
          simp only [Finset.mem_singleton, exists_eq_left]
          exact and_comm
  have hall_ok : ∀ it ∈ allItems,
      (∀ bw, it.2.1 = some bw → bw < n + gs1.length) ∧ (it.2.1.isSome ∨ it.2.2 ≠ []) := by
    intro it hit
    simp only [allItems, topItems, newItems, List.mem_append, List.mem_map, Finset.mem_toList] at hit
    rcases hit with ⟨a, ha, rfl⟩ | ⟨v, hv, rfl⟩
    · have h := htopItem_ok a ha
      exact ⟨h.1, Or.inl h.2.1⟩
    · refine ⟨fun bw hbw => (by cases hbw), Or.inr ?_⟩
      intro hemp
      simp only [List.map_eq_nil_iff] at hemp
      obtain ⟨u, hu⟩ := hLne v (Finset.mem_sdiff.mp hv).1
      have : u ∈ (L v).toList := Finset.mem_toList.mpr hu
      rw [hemp] at this; cases this
  obtain ⟨⟨ex2, hex2⟩, hlen2, hwlen2, hAO2, hlt2, hval2⟩ := addStars_spec hAO1 allItems hall_ok
  set gs2 := (addStars n gs1 allItems).1
  set topWires := (addStars n gs1 allItems).2
  have hall_ne : allItems ≠ [] := by
    intro hemp
    have hSemp : S_tops = ∅ := by
      have h1 : topItems = [] := (List.append_eq_nil_iff.mp hemp).1
      simp only [topItems, List.map_eq_nil_iff] at h1
      ext a; simp only [Finset.notMem_empty, iff_false]
      intro ha; have := Finset.mem_toList.mpr ha; rw [h1] at this; cases this
    have hNemp : Zact \ Zhas = ∅ := by
      have h2 : newItems = [] := (List.append_eq_nil_iff.mp hemp).2
      simp only [newItems, List.map_eq_nil_iff] at h2
      ext v; simp only [Finset.notMem_empty, iff_false]
      intro hv; have := Finset.mem_toList.mpr hv; rw [h2] at this; cases this
    have hZhas_emp : Zhas = ∅ := by
      ext v; simp only [Finset.notMem_empty, iff_false]
      intro hv; have := htop_mem v hv; rw [hSemp] at this; exact Finset.notMem_empty _ this
    have hZact_emp : Zact = ∅ := by
      rw [hZhas_emp, Finset.sdiff_empty] at hNemp; exact hNemp
    obtain ⟨u, v, huv⟩ := hne
    have he_mem : s(u, v) ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.mpr huv
    have hst_emp : starEdges G C = ∅ := by
      ext e; simp only [Finset.notMem_empty, iff_false, starEdges, Finset.mem_biUnion,
        Finset.mem_image, Finset.mem_product]
      rintro ⟨a, ha, ⟨p, ⟨hp0, hp1⟩, _⟩⟩
      have haS : a ∈ S_tops := by
        rw [Finset.mem_sdiff]; refine ⟨ha, fun hc => ?_⟩
        rw [centreless, Finset.mem_filter] at hc
        rcases hc.2 with h0 | h1
        · rw [h0] at hp0; exact Finset.notMem_empty _ hp0
        · rw [h1] at hp1; exact Finset.notMem_empty _ hp1
      rw [hSemp] at haS; exact Finset.notMem_empty _ haS
    have hu_mem : s(u, v) ∈ Ustar G C := by unfold Ustar; rw [hst_emp, Finset.sdiff_empty]; exact he_mem
    obtain ⟨w, hw, _⟩ := hUcov _ hu_mem
    rw [hZact_emp] at hw; exact Finset.notMem_empty _ hw
  have htw_ne : topWires ≠ [] := by
    intro h; rw [h] at hwlen2; exact hall_ne (List.eq_nil_of_length_eq_zero hwlen2.symm)
  obtain ⟨hAO3, hlt3⟩ := appendOrList_isAO2 hAO2 topWires htw_ne hlt2
  let C' : Circuit := ⟨(appendOrList n gs2 topWires).1, (appendOrList n gs2 topWires).2⟩
  have hAO' : IsAO2 n C' := hAO3
  have hfun' : circuitFun n C' = graphFun G ∅ := by
    funext x
    change wval ⟨(appendOrList n gs2 topWires).1, 0⟩ x (appendOrList n gs2 topWires).2 = graphFun G ∅ x
    rw [appendOrList_wval hAO2 x topWires htw_ne hlt2]
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq, hval2 x, graphFun_iff]
    constructor
    · rintro ⟨it, hit, hxv, hbody⟩
      simp only [allItems, topItems, newItems, List.mem_append, List.mem_map, Finset.mem_toList] at hit
      rcases hit with ⟨a, ha, rfl⟩ | ⟨v, hv, rfl⟩
      · have hiff := (htopItem_ok a ha).2.2 x
        rcases hiff.mp ⟨hxv, hbody⟩ with ⟨⟨u0, hu0, hxu0⟩, ⟨u1, hu1, hxu1⟩⟩ | ⟨v, hv, _, hxv', u, hu, hxu⟩
        · exact ⟨u0, u1, top_sides_adj hL.1 (Finset.mem_sdiff.mp ha).1 hu0 hu1, hxu0, hxu1⟩
        · exact ⟨v, u, hLadj v (hZsub hv) u hu, hxv', hxu⟩
      · rcases hbody with ⟨bw, hbw, _⟩ | ⟨u, hu, hxu⟩
        · cases hbw
        · rw [Finset.mem_toList] at hu
          exact ⟨v, u, hLadj v (Finset.mem_sdiff.mp hv).1 u hu, hxv, hxu⟩
    · rintro ⟨u, v, huv, hxu, hxv⟩
      have he : s(u, v) ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.mpr huv
      by_cases hst : s(u, v) ∈ starEdges G C
      · simp only [starEdges, Finset.mem_biUnion, Finset.mem_image, Finset.mem_product] at hst
        rcases hst with ⟨a, ha, ⟨p0, p1⟩, ⟨hp0, hp1⟩, hpeq⟩
        have haS : a ∈ S_tops := by
          rw [Finset.mem_sdiff]; refine ⟨ha, fun hc => ?_⟩
          rw [centreless, Finset.mem_filter] at hc
          rcases hc.2 with h0 | h1
          · rw [h0] at hp0; exact Finset.notMem_empty _ hp0
          · rw [h1] at hp1; exact Finset.notMem_empty _ hp1
        refine ⟨mkTopItem a, ?_, ?_⟩
        · simp only [allItems, topItems, List.mem_append, List.mem_map, Finset.mem_toList]
          exact Or.inl ⟨a, haS, rfl⟩
        · apply ((htopItem_ok a haS).2.2 x).mpr
          left
          rw [Sym2.eq_iff] at hpeq
          rcases hpeq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨⟨p0, hp0, hxu⟩, ⟨p1, hp1, hxv⟩⟩
          · exact ⟨⟨p0, hp0, hxv⟩, ⟨p1, hp1, hxu⟩⟩
      · have hu_mem : s(u, v) ∈ Ustar G C := Finset.mem_sdiff.mpr ⟨he, hst⟩
        obtain ⟨w, hw, z, hz, heq⟩ := hUcov _ hu_mem
        rw [Sym2.eq_iff] at heq
        have hxw : x w = true := by rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
        have hxz : x z = true := by rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
        by_cases hwh : w ∈ Zhas
        · refine ⟨mkTopItem (topOf w), ?_, ?_⟩
          · simp only [allItems, topItems, List.mem_append, List.mem_map, Finset.mem_toList]
            exact Or.inl ⟨topOf w, htop_mem w hwh, rfl⟩
          · apply ((htopItem_ok (topOf w) (htop_mem w hwh)).2.2 x).mpr
            right
            exact ⟨w, hwh, rfl, hxw, z, hz, hxz⟩
        · refine ⟨(w, none, (L w).toList), ?_, hxw, Or.inr ⟨z, Finset.mem_toList.mpr hz, hxz⟩⟩
          simp only [allItems, newItems, List.mem_append, List.mem_map, Finset.mem_toList]
          exact Or.inr ⟨w, Finset.mem_sdiff.mpr ⟨hw, hwh⟩, rfl⟩
  -- Now compute C'.size and compare with C.size!
  have hsum_top : (topItems.map fun it => it.2.2.length + (if it.2.1.isSome then 1 else 0)).sum =
      (∑ v ∈ Zhas, (L v).card) + S_tops.card := by
    have hmap : (topItems.map fun it => it.2.2.length + (if it.2.1.isSome then 1 else 0)).sum =
        ∑ a ∈ S_tops, ((mkTopItem a).2.2.length + 1) := by
      simp only [topItems, List.map_map]
      rw [← Finset.sum_map_toList]
      congr 1
      apply List.map_congr_left
      intro a ha
      rw [Finset.mem_toList] at ha
      simp only [Function.comp_apply, (htopItem_ok a ha).2.1, ↓reduceIte]
    rw [hmap, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
    congr 1
    have hsum_L : ∑ a ∈ S_tops, (mkTopItem a).2.2.length =
        ∑ a ∈ S_tops, if h : ∃ v ∈ Zhas, topOf v = a then (L (Classical.choose h)).card else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      by_cases h : ∃ v ∈ Zhas, topOf v = a
      · simp only [mkTopItem, dif_pos h, Finset.length_toList]
      · simp only [mkTopItem, dif_neg h, dif_pos ha]
        split_ifs <;> rfl
    rw [hsum_L]
    have himg_sub : Zhas.image topOf ⊆ S_tops := by
      intro a ha; simp only [Finset.mem_image] at ha; rcases ha with ⟨v, hv, rfl⟩; exact htop_mem v hv
    rw [← Finset.sum_subset himg_sub]
    · rw [Finset.sum_image (fun v1 hv1 v2 hv2 heq => htop_inj v1 hv1 v2 hv2 heq)]
      apply Finset.sum_congr rfl
      intro v hv
      have hex : ∃ v' ∈ Zhas, topOf v' = topOf v := ⟨v, hv, rfl⟩
      rw [dif_pos hex]
      have hch := Classical.choose_spec hex
      rw [htop_inj _ hch.1 v hv hch.2]
    · intro a _ hnot
      rw [dif_neg]
      rintro ⟨v, hv, rfl⟩
      exact hnot (Finset.mem_image_of_mem topOf hv)
  have hsum_new : (newItems.map fun it => it.2.2.length + (if it.2.1.isSome then 1 else 0)).sum =
      ∑ v ∈ Zact \ Zhas, (L v).card := by
    simp only [newItems, List.map_map]
    rw [← Finset.sum_map_toList]
    congr 1
    apply List.map_congr_left
    intro v _
    simp [Finset.length_toList]
  have hsum_all : (allItems.map fun it => it.2.2.length + (if it.2.1.isSome then 1 else 0)).sum =
      (∑ v ∈ Zact, (L v).card) + S_tops.card := by
    simp only [allItems, List.map_append, List.sum_append, hsum_top, hsum_new]
    have hsplit : ∑ v ∈ Zact, (L v).card = (∑ v ∈ Zhas, (L v).card) + (∑ v ∈ Zact \ Zhas, (L v).card) := by
      rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hZsub]
    omega
  have hlen_all : allItems.length = S_tops.card + (Zact \ Zhas).card := by
    simp [allItems, topItems, newItems]
  have hC'_size : C'.size =
      (lam G C).card + (∑ v ∈ Zact, (L v).card) + 2 * S_tops.card + (Zact \ Zhas).card - 1 := by
    change (appendOrList n gs2 topWires).1.length = _
    rw [appendOrList_len n gs2 topWires htw_ne, hwlen2, hlen_all, hlen2, hgs1_len, hsum_all]
    have hpos : 0 < S_tops.card + (Zact \ Zhas).card := by
      rw [← hlen_all]; exact List.length_pos_of_ne_nil hall_ne
    omega
  have hsz_le : C.size ≤ C'.size := hL.2.2 C' hAO' hfun'
  have hpart := circuit_size_partition hL
  have horT := tops_le_orT_add_one hL hLift hne
  have hjunk_card : (junk G C).card = 2 := by
    have : junk G C = {g1, g2} := by ext k; simp [hjunk]
    rw [this, Finset.card_pair hg12]
  have hcent_sub : centreless G C ⊆ tops G C := Finset.filter_subset _ _
  have htops_split : (tops G C).card = S_tops.card + (centreless G C).card := by
    rw [card_sdiff_eq hcent_sub]; have := Finset.card_le_card hcent_sub; omega
  have hlam_sub : lam G C ⊆ orN G C := Finset.filter_subset _ _
  have horN_split : (orN G C).card = (lam G C).card + (orN G C \ lam G C).card := by
    rw [card_sdiff_eq hlam_sub]; have := Finset.card_le_card hlam_sub; omega
  omega

end Surgery


namespace MutualBudget

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

-- Circuit evaluation and OR reachability follow L_meta_1490 and L_meta_4901.
def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false
lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj
lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [ite_eq_right hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h'; exact ⟨hlt, h'⟩
    · rw [ite_eq_right hlt] at h'; cases h'
  · intro h i hi
    rw [ite_eq_left (h i hi).1]; exact (h i hi).2
lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j) := rfl

def OrStep (n : ℕ) (C : Circuit) (w w' : ℕ) : Prop :=
  ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
    w' ∈ (gateAt C k).inputs ∧ w' < n + k

lemma orStep_up {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') (hv : val C x w' = true) :
    val C x w = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head hstep _ ih =>
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (val_or hx hk hop).mpr ⟨_, hin, hlt, ih⟩

lemma or_trace {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) :
    ∀ w : ℕ, val C x w = true →
      ∃ w', Relation.ReflTransGen (OrStep n C) w w' ∧ val C x w' = true ∧
        (w' < n ∨ ∃ h, h < C.gates.length ∧ w' = n + h ∧ (gateAt C h).op ≠ GateOp.or) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · exact ⟨w, Relation.ReflTransGen.refl, hv, Or.inl hw⟩
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [val_ge hx hlen] at hv; cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        by_cases hop : (gateAt C k).op = GateOp.or
        · obtain ⟨i, hin, hlt, hi⟩ := (val_or hx hk hop).mp hv
          obtain ⟨w', hr, hv', hw'⟩ := ih i hlt hi
          exact ⟨w', Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hin, hlt⟩ hr, hv', hw'⟩
        · exact ⟨n + k, Relation.ReflTransGen.refl, hv, Or.inr ⟨k, hk, rfl, hop⟩⟩

lemma pairInput_left {n : ℕ} (u v : Fin n) : pairInput u v u = true := by
  simp [pairInput]

lemma pairInput_right {n : ℕ} (u v : Fin n) : pairInput u v v = true := by
  simp [pairInput]

lemma pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
  simp [pairInput]

lemma graphFun_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, pairInput_true]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro h
    exact ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩
lemma operand_trace {n : ℕ} {C : Circuit} (u v : Fin n) (p : ℕ)
    (hv : val C (List.ofFn (pairInput u v)) p = true) :
    (∃ t : Fin n, (t = u ∨ t = v) ∧ Relation.ReflTransGen (OrStep n C) p t.val) ∨
    (∃ h, h < C.gates.length ∧ (gateAt C h).op ≠ GateOp.or ∧
      Relation.ReflTransGen (OrStep n C) p (n + h) ∧
      val C (List.ofFn (pairInput u v)) (n + h) = true) := by
  obtain ⟨w', hr, hv', hw'⟩ := or_trace (n := n) (C := C) (x := List.ofFn (pairInput u v))
    (by simp) p hv
  rcases hw' with hlt | ⟨h, hh, rfl, hop⟩
  · left
    refine ⟨⟨w', hlt⟩, ?_, hr⟩
    have h1 := val_ofFn C (pairInput u v) ⟨w', hlt⟩
    rw [show (⟨w', hlt⟩ : Fin n).val = w' from rfl, hv'] at h1
    exact (pairInput_true u v _).mp h1.symm
  · right
    exact ⟨h, hh, hop, hr, hv'⟩

lemma reach_var_val {n : ℕ} {C : Circuit} (x : Fin n → Bool) (p : ℕ) (t : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p t.val) (ht : x t = true) :
    val C (List.ofFn x) p = true :=
  orStep_up (n := n) (by simp) hr (by rw [val_ofFn]; exact ht)
lemma edge_trace {n : ℕ} (G : SimpleGraph (Fin n)) {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hF : ∀ u v : Fin n, F (pairInput u v) = true → G.Adj u v)
    (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x)
    (u v : Fin n) (huv : F (pairInput u v) = true) :
    ∃ a, a < C.gates.length ∧ (gateAt C a).op ≠ GateOp.or ∧
      Relation.ReflTransGen (OrStep n C) C.output (n + a) ∧
      val C (List.ofFn (pairInput u v)) (n + a) = true := by
  rcases operand_trace (C := C) u v C.output (by rw [hout]; exact huv) with
    ⟨t, _, hr⟩ | h
  · exfalso
    have h1 := reach_var_val (pairInput t t) _ t hr (pairInput_left t t)
    rw [hout] at h1
    exact G.irrefl (hF t t h1)
  · exact h

lemma below_of_reach {n : ℕ} {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x) (a : ℕ)
    (hr : Relation.ReflTransGen (OrStep n C) C.output (n + a)) (x : Fin n → Bool)
    (hv : val C (List.ofFn x) (n + a) = true) : F x = true := by
  rw [← hout]
  exact orStep_up (n := n) (by simp) hr hv
lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

lemma orStep_le {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') : w' ≤ w := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact le_rfl
  | head hstep _ ih =>
    obtain ⟨k, _, rfl, _, _, hlt⟩ := hstep
    omega

lemma orStep_cone {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') :
    ∀ k h', w = n + k → w' = n + h' → h' = k ∨ InCone n C h' k := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => intro k h' h1 h2; left; omega
  | @head a c hstep hrest ih =>
    intro k h' h1 h2
    obtain ⟨k0, hk0, e, _, hin, hlt⟩ := hstep
    have hk : k0 = k := by omega
    subst hk
    have hle := orStep_le hrest
    obtain ⟨k1, hk1⟩ : ∃ k1, c = n + k1 := ⟨c - n, by omega⟩
    subst hk1
    right
    rw [inCone_iff]
    exact ⟨hk0, k1, by omega, hin, ih k1 h' rfl h2⟩

lemma operand_cone {n : ℕ} {C : Circuit} {a p h : ℕ} (ha : a < C.gates.length)
    (hin : p ∈ (gateAt C a).inputs) (hp : p < n + a)
    (hr : Relation.ReflTransGen (OrStep n C) p (n + h)) : InCone n C h a := by
  have hle := orStep_le hr
  obtain ⟨k1, rfl⟩ : ∃ k1, p = n + k1 := ⟨p - n, by omega⟩
  rw [inCone_iff]
  exact ⟨ha, k1, by omega, hin, orStep_cone hr k1 h rfl rfl⟩
lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (orStep n (gs.foldl (orStep n) []) g).getD k [] =
          (gs.foldl (orStep n) []).getD k [] := by
      intro k hk
      simp only [orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
        simp only [orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold OrReaches orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

lemma reach_orReaches {n : ℕ} {C : Circuit} {w w2 : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w2) :
    ∀ g, w2 = n + g → g < C.gates.length → OrReaches n C w g := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro g h1 hg
    subst h1
    exact (orReaches_iff n C g g).mpr ⟨hg, Or.inl rfl⟩
  | @head a c hstep hrest ih =>
    intro g h1 hg
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (orReaches_iff n C k g).mpr ⟨hk, Or.inr ⟨hop, c, hin, hlt, ih g h1 hg⟩⟩

lemma orReaches_reach {n : ℕ} {C : Circuit} (g : ℕ) :
    ∀ w, OrReaches n C w g →
      Relation.ReflTransGen (OrStep n C) w (n + g) ∧ g < C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    have hnw : n ≤ w := h.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp h
    rcases h3 with rfl | ⟨hop, i, hi, hlt, hr⟩
    · exact ⟨Relation.ReflTransGen.refl, hk⟩
    · obtain ⟨hr2, hg⟩ := ih i hlt hr
      exact ⟨Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hi, hlt⟩ hr2, hg⟩

lemma mem_orIn_reach {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hu : u ∈ PEqualNP.TopForm.orIn n C p) :
    Relation.ReflTransGen (OrStep n C) p u.val := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  rcases hu with h | ⟨k, hk, hr, hop, hin⟩
  · rw [h]
  · exact (orReaches_reach k p hr).1.tail ⟨k, hk, rfl, hop, hin, by omega⟩

lemma reach_mem_orIn {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p u.val) :
    u ∈ PEqualNP.TopForm.orIn n C p := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases Relation.ReflTransGen.cases_tail hr with h | ⟨c, hpc, hstep⟩
  · exact Or.inl h
  · obtain ⟨k, hk, rfl, hop, hin, _⟩ := hstep
    exact Or.inr ⟨k, hk, reach_orReaches hpc k rfl hk, hop, hin⟩

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

lemma topData {a : ℕ} (ha : a ∈ tops G C) :
    a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧ BelowF G C a := by
  simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using ha
lemma junkData {a : ℕ} (ha : a ∈ junk G C) :
    a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧
      ∃ x : Fin n → Bool, gateVal n C a x = true ∧ graphFun G ∅ x = false := by
  rcases Finset.mem_filter.mp ha with ⟨hr, hop, hal, hd⟩
  exact ⟨hal, hop, hd⟩
lemma binaryInputs (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) :
    ∃ p q, (gateAt C a).inputs = [p, q] :=
  List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem ha))
lemma opndMem (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    opnd C a b ∈ (gateAt C a).inputs := by
  obtain ⟨p, q, hpq⟩ := binaryInputs hAO ha
  fin_cases b <;> simp [opnd, hpq]
lemma opndBound (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    opnd C a b < n + a :=
  hAO.2.1 a ha _ (opndMem hAO ha b)
lemma andValBoth (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and) (x : Fin n → Bool) :
    gateVal n C a x = true ↔
      val C (List.ofFn x) (opnd C a 0) = true ∧
      val C (List.ofFn x) (opnd C a 1) = true := by
  rw [gateVal_eq_val, val_and (n := n) (by simp) ha hop]
  constructor
  · intro h
    exact ⟨(h _ (opndMem hAO ha 0)).2, (h _ (opndMem hAO ha 1)).2⟩
  · intro h i hi
    refine ⟨hAO.2.1 a ha i hi, ?_⟩
    obtain ⟨p, q, hpq⟩ := binaryInputs hAO ha
    rcases List.mem_cons.mp (hpq ▸ hi) with rfl | hq
    · simpa [opnd, hpq] using h.1
    · have e : i = q := List.mem_singleton.mp hq
      subst i
      simpa [opnd, hpq] using h.2
lemma andValOperands (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and) (x : Fin n → Bool) :
    gateVal n C a x = true ↔ ∀ b : Fin 2, val C (List.ofFn x) (opnd C a b) = true := by
  rw [andValBoth hAO ha hop]
  constructor
  · intro h b
    fin_cases b
    · exact h.1
    · exact h.2
  · intro h
    exact ⟨h 0, h 1⟩
lemma operandReachCone (hAO : IsAO2 n C) {a h : ℕ} (ha : a < C.gates.length)
    {b : Fin 2} (hr : OrReaches n C (opnd C a b) h) :
    InCone n C h a :=
  operand_cone ha (opndMem hAO ha b) (opndBound hAO ha b)
    (orReaches_reach h _ hr).1
lemma operandReachLt (hAO : IsAO2 n C) {a h : ℕ} (ha : a < C.gates.length)
    {b : Fin 2} (hr : OrReaches n C (opnd C a b) h) : h < a := by
  have hle := orStep_le (orReaches_reach h _ hr).1
  have hb := opndBound hAO ha b
  omega
lemma operandOrAndJunk (hAO : IsAO2 n C) (hT : TopForm G C) {a h : ℕ}
    (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and)
    {b : Fin 2} (hr : OrReaches n C (opnd C a b) h)
    (hh : (gateAt C h).op = GateOp.and) : h ∈ junk G C := by
  have hlen := (orReaches_reach h _ hr).2
  have hnb : ¬ BelowF G C h :=
    fun hb => hT h hlen a ha hh hb hop (operandReachCone hAO ha hr)
  have hdirty : ∃ x : Fin n → Bool, gateVal n C h x = true ∧ graphFun G ∅ x = false := by
    by_contra hne
    apply hnb
    intro x hx
    by_contra hf
    exact hne ⟨x, hx, Bool.eq_false_iff.mpr hf⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlen, hh, hlen, hdirty⟩
lemma reachVal {w h : ℕ} {x : Fin n → Bool} (hr : OrReaches n C w h)
    (hh : gateVal n C h x = true) : val C (List.ofFn x) w = true :=
  orStep_up (n := n) (by simp) (orReaches_reach h _ hr).1 hh
lemma eitherOperand (b c : Fin 2) : c = b ∨ c = 1 - b := by
  fin_cases b <;> fin_cases c <;> decide
lemma oppositeSideWmax (hAO : IsAO2 n C) {a j : ℕ} (ha : a ∈ tops G C) {b : Fin 2}
    (hr : OrReaches n C (opnd C a b) j) :
    side (n := n) C a (1 - b) ⊆ wmax G C j := by
  intro t ht
  obtain ⟨hal, hao, hab⟩ := topData ha
  simp only [wmax, Finset.mem_filter, Finset.mem_univ, true_and]
  intro x hj hx
  apply hab x
  apply (andValOperands hAO hal hao x).mpr
  intro c
  rcases eitherOperand b c with rfl | rfl
  · exact reachVal hr hj
  · exact reach_var_val x _ t (mem_orIn_reach t ht) hx
lemma orInTrans {w z : ℕ} (hr : Relation.ReflTransGen (OrStep n C) w z) :
    orIn n C z ⊆ orIn n C w :=
  fun x hx => reach_mem_orIn x (hr.trans (mem_orIn_reach x hx))
lemma orStepOpnd (hAO : IsAO2 n C) {m : ℕ} (hm : m < C.gates.length)
    (hop : (gateAt C m).op = GateOp.or) (b : Fin 2) :
    OrStep n C (n + m) (opnd C m b) :=
  ⟨m, hm, rfl, hop, opndMem hAO hm b, opndBound hAO hm b⟩
lemma inputsAsOpnd (hAO : IsAO2 n C) {m z : ℕ} (hm : m < C.gates.length)
    (hz : z ∈ (gateAt C m).inputs) : ∃ b : Fin 2, z = opnd C m b := by
  obtain ⟨p, q, hpq⟩ := binaryInputs hAO hm
  rcases List.mem_cons.mp (hpq ▸ hz) with rfl | hq
  · exact ⟨0, by simp [opnd, hpq]⟩
  · have e : z = q := List.mem_singleton.mp hq
    exact ⟨1, by simpa [opnd, hpq] using e⟩
lemma orNOfRaw {m : ℕ} (hm : m < C.gates.length) (hop : (gateAt C m).op = GateOp.or)
    (hn : (orIn n C (n + m)).Nonempty) : m ∈ orN G C := by
  obtain ⟨t, ht⟩ := hn
  simp only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range]
  refine ⟨hm, hop, ?_⟩
  intro hb
  have hv : gateVal n C m (pairInput t t) = true :=
    reach_var_val (pairInput t t) _ t (mem_orIn_reach t ht) (pairInput_left t t)
  exact G.irrefl ((graphFun_pair G t t).mp (hb _ hv))
lemma lamAvoidsUstar {m : ℕ} (hm : m ∈ lam G C)
    (hstar : ∀ a ∈ tops G C, ∀ x ∈ side (n := n) C a 0, ∀ y ∈ side C a 1, G.Adj x y) :
    ∃ t : Fin n, ∀ x ∈ orIn n C (n + m), G.Adj t x ∧ s(t, x) ∉ Ustar G C := by
  obtain ⟨_, _, _, a, ha, b, hcard, hr⟩ := Finset.mem_filter.mp hm
  have hsub : orIn n C (n + m) ⊆ side (n := n) C a b :=
    orInTrans (orReaches_reach m _ hr).1
  obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hcard
  refine ⟨t, fun x hx => ?_⟩
  have hts : t ∈ side (n := n) C a (1 - b) := by simp [ht]
  have hstar' : s(t, x) ∈ starEdges G C := by
    unfold starEdges
    refine Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr ?_⟩
    fin_cases b
    · exact ⟨(x, t), Finset.mem_product.mpr ⟨hsub hx, hts⟩, Sym2.eq_swap⟩
    · exact ⟨(t, x), Finset.mem_product.mpr ⟨hts, hsub hx⟩, rfl⟩
  refine ⟨?_, fun he => (Finset.mem_sdiff.mp he).2 hstar'⟩
  fin_cases b
  · exact (hstar a ha x (hsub hx) t hts).symm
  · exact hstar a ha t hts x (hsub hx)

lemma sideVal {a : ℕ} {b : Fin 2} {x : Fin n → Bool} {t : Fin n}
    (ht : t ∈ side (n := n) C a b) (hx : x t = true) :
    val C (List.ofFn x) (opnd C a b) = true :=
  reach_var_val x _ t (mem_orIn_reach t ht) hx

lemma andFromInputs (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and) {x : Fin n → Bool}
    {u v : Fin n} (hu : u ∈ side (n := n) C a 0) (hv : v ∈ side (n := n) C a 1)
    (xu : x u = true) (xv : x v = true) : gateVal n C a x = true :=
  (andValBoth hAO ha hop x).mpr ⟨sideVal hu xu, sideVal hv xv⟩

lemma topAdj (hAO : IsAO2 n C) {a : ℕ} (ha : a ∈ tops G C)
    {u v : Fin n} (hu : u ∈ side (n := n) C a 0) (hv : v ∈ side (n := n) C a 1) :
    G.Adj u v := by
  obtain ⟨hl, ho, hb⟩ := topData ha
  exact (graphFun_pair G u v).mp
    (hb _ (andFromInputs hAO hl ho hu hv (pairInput_left u v) (pairInput_right u v)))

lemma acceptedTop (hL : IsLeastAO G C) {u v : Fin n} (hadj : G.Adj u v) :
    ∃ a ∈ tops G C, gateVal n C a (pairInput u v) = true := by
  have hout (x : Fin n → Bool) : val C (List.ofFn x) C.output = graphFun G ∅ x :=
    congrFun hL.2.1 x
  obtain ⟨a, hl, ho, hr, hv⟩ :=
    edge_trace G (graphFun G ∅) (fun k l => (graphFun_pair G k l).mp)
      hout u v ((graphFun_pair G u v).mpr hadj)
  have hand := (hL.1.1 _ (gateAt_mem hl)).resolve_right ho
  have hb : BelowF G C a := fun x hx =>
    below_of_reach (graphFun G ∅) hout a hr x (gateVal_eq_val n C a x ▸ hx)
  refine ⟨a, ?_, hv⟩
  simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using
    And.intro hl (And.intro hand hb)

lemma operandSupport (hAO : IsAO2 n C) (hT : TopForm G C) {a : ℕ}
    (ha : a < C.gates.length) (ho : (gateAt C a).op = GateOp.and) {b : Fin 2}
    {u v : Fin n} (h : val C (List.ofFn (pairInput u v)) (opnd C a b) = true) :
    (∃ t ∈ side (n := n) C a b, t = u ∨ t = v) ∨
      ∃ j ∈ junk G C, OrReaches n C (opnd C a b) j ∧
        gateVal n C j (pairInput u v) = true := by
  rcases operand_trace (C := C) u v _ h with ⟨t, ht, hr⟩ | ⟨j, hj, hn, hr, hv⟩
  · exact .inl ⟨t, reach_mem_orIn t hr, ht⟩
  · have hr' := reach_orReaches hr j rfl hj
    exact .inr ⟨j, operandOrAndJunk hAO hT ha ho hr'
      ((hAO.1 _ (gateAt_mem hj)).resolve_right hn), hr', hv⟩

def coveredByJunk (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) :
    Finset (Sym2 (Fin n)) :=
  (junk G C).biUnion fun j => (gammaE G C j).filter fun e =>
    ¬ Disjoint e.toFinset (wmax G C j)

def Joint (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (j k : ℕ) : Prop :=
  ∀ x : Fin n → Bool, gateVal n C j x = true → gateVal n C k x = true →
    graphFun G ∅ x = true

lemma joint_comm {j k : ℕ} (h : Joint G C j k) : Joint G C k j :=
  fun x hk hj => h x hj hk

lemma freeOfWmax {u v : Fin n} (he : s(u,v) ∈ Ustar G C \ coveredByJunk G C)
    {j : ℕ} (hj : j ∈ junk G C) (hval : gateVal n C j (pairInput u v) = true)
    {t : Fin n} (ht : t = u ∨ t = v) : t ∉ wmax G C j := by
  intro hw
  apply (Finset.mem_sdiff.mp he).2
  refine Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
  · exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp (Finset.mem_sdiff.mp he).1).1,
      u, v, rfl, hval⟩
  · intro hd
    exact (Finset.disjoint_left.mp hd) (by simpa using ht) hw

lemma memJunkPair {j k a : ℕ} (hs : junk G C = {j,k}) (ha : a ∈ junk G C) :
    a = j ∨ a = k := by
  simpa only [hs, Finset.mem_insert, Finset.mem_singleton] using ha

lemma residualJoint (hL : IsLeastAO G C) (hT : TopForm G C) {j k : ℕ}
    (hs : junk G C = {j,k}) {u v : Fin n}
    (he : s(u,v) ∈ Ustar G C \ coveredByJunk G C) :
    Joint G C j k ∧ gateVal n C j (pairInput u v) = true ∧
      gateVal n C k (pairInput u v) = true := by
  have hU := (Finset.mem_sdiff.mp he).1
  have hadj : G.Adj u v := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp hU).1
  obtain ⟨a, ha, hv⟩ := acceptedTop hL hadj
  obtain ⟨hl, ho, hb⟩ := topData ha
  have traces (b : Fin 2) := operandSupport hL.1 hT hl ho
    ((andValOperands hL.1 hl ho (pairInput u v)).mp hv b)
  have mixed {b : Fin 2} {t : Fin n} {g : ℕ}
      (ht : t ∈ side (n := n) C a (1-b)) (het : t = u ∨ t = v)
      (hg : g ∈ junk G C) (hr : OrReaches n C (opnd C a b) g)
      (hgval : gateVal n C g (pairInput u v) = true) : False :=
    freeOfWmax he hg hgval het (oppositeSideWmax hL.1 ha hr ht)
  rcases traces 0 with ⟨x,hx,hxe⟩ | ⟨g,hg,hrg,hvg⟩ <;>
    rcases traces 1 with ⟨y,hy,hye⟩ | ⟨g',hg',hrg',hvg'⟩
  · have hxy := G.ne_of_adj (topAdj hL.1 ha hx hy)
    have eq : s(u,v) = s(x,y) := by
      rcases hxe with rfl | rfl <;> rcases hye with rfl | rfl
      · exact (hxy rfl).elim
      · rfl
      · exact Sym2.eq_swap
      · exact (hxy rfl).elim
    exact ((Finset.mem_sdiff.mp hU).2 (eq ▸ Finset.mem_biUnion.mpr ⟨a,ha,
      Finset.mem_image.mpr ⟨(x,y), Finset.mem_product.mpr ⟨hx,hy⟩, rfl⟩⟩)).elim
  · exact (mixed (b := 1) (by exact hx) hxe hg' hrg' hvg').elim
  · exact (mixed (b := 0) (by exact hy) hye hg hrg hvg).elim
  · have pair : Joint G C g g' := fun x xv yv =>
      hb x ((andValBoth hL.1 hl ho x).mpr ⟨reachVal hrg xv, reachVal hrg' yv⟩)
    have ne : g ≠ g' := by
      rintro rfl
      obtain ⟨_,_,x,hx,hfx⟩ := junkData hg
      exact Bool.false_ne_true (hfx.symm.trans (pair x hx hx))
    rcases memJunkPair hs hg with eg | eg <;> rcases memJunkPair hs hg' with eg' | eg'
    · exact (ne (eg.trans eg'.symm)).elim
    · simpa only [eg, eg'] using And.intro pair (And.intro hvg hvg')
    · simpa only [eg, eg'] using And.intro (joint_comm pair) (And.intro hvg' hvg)
    · exact (ne (eg.trans eg'.symm)).elim

lemma junkInputHits (hAO : IsAO2 n C) (hT : TopForm G C) {j k : ℕ}
    (hs : junk G C = {j,k}) (joint : Joint G C j k) {u v : Fin n}
    (he : s(u,v) ∈ Ustar G C \ coveredByJunk G C)
    (hjval : gateVal n C j (pairInput u v) = true)
    (hkval : gateVal n C k (pairInput u v) = true) (b : Fin 2) :
    ∃ t ∈ side (n := n) C j b, t = u ∨ t = v := by
  have hj : j ∈ junk G C := by simp [hs]
  have hk : k ∈ junk G C := by simp [hs]
  obtain ⟨hl,ho,_⟩ := junkData hj
  have trace (i : Fin 2) := operandSupport hAO hT hl ho
    ((andValOperands hAO hl ho (pairInput u v)).mp hjval i)
  have other {i g} (hg : g ∈ junk G C) (hr : OrReaches n C (opnd C j i) g) : g = k :=
    (memJunkPair hs hg).resolve_left (fun eq => (Nat.ne_of_lt (operandReachLt hAO hl hr)) eq)
  have makeJ {x : Fin n → Bool}
      (l : val C (List.ofFn x) (opnd C j b) = true)
      (r : val C (List.ofFn x) (opnd C j (1-b)) = true) : gateVal n C j x = true :=
    (andValOperands hAO hl ho x).mpr (fun i => by
      rcases eitherOperand b i with rfl | rfl
      · exact l
      · exact r)
  rcases trace b with h | ⟨g,hg,hr,_⟩
  · exact h
  · have eg := other hg hr
    subst g
    exfalso
    rcases trace (1-b) with ⟨t,ht,et⟩ | ⟨g,hg,hr',_⟩
    · apply freeOfWmax he hk hkval et
      simp only [wmax, Finset.mem_filter, Finset.mem_univ, true_and]
      intro x hx xt
      exact joint x (makeJ (reachVal hr hx) (sideVal ht xt)) hx
    · have eg := other hg hr'
      subst g
      obtain ⟨_,_,x,hx,hfx⟩ := junkData hk
      exact Bool.false_ne_true (hfx.symm.trans
        (joint x (makeJ (reachVal hr hx) (reachVal hr' hx)) hx))

def exclusive (C : Circuit) (j : ℕ) (b : Fin 2) : Finset (Fin n) :=
  side C j b \ side C j (1-b)

lemma exclusiveDisjoint {j : ℕ} {t : Fin n} {b : Fin 2}
    (ht : t ∈ exclusive (n := n) C j b) (ht' : t ∈ side (n := n) C j (1-b)) : False :=
  (Finset.mem_sdiff.mp ht).2 ht'

lemma junkOrientation (hAO : IsAO2 n C) (hT : TopForm G C) {j k : ℕ}
    (hs : junk G C = {j,k}) (joint : Joint G C j k) {u v : Fin n}
    (he : s(u,v) ∈ Ustar G C \ coveredByJunk G C)
    (hjval : gateVal n C j (pairInput u v) = true)
    (hkval : gateVal n C k (pairInput u v) = true) :
    (u ∈ exclusive (n := n) C j 0 ∧ v ∈ exclusive (n := n) C j 1) ∨
    (v ∈ exclusive (n := n) C j 0 ∧ u ∈ exclusive (n := n) C j 1) := by
  have hj : j ∈ junk G C := by simp [hs]
  have hk : k ∈ junk G C := by simp [hs]
  obtain ⟨hl,ho,_⟩ := junkData hj
  have disj {t : Fin n} (ht : t = u ∨ t = v)
      (h0 : t ∈ side (n := n) C j 0) (h1 : t ∈ side (n := n) C j 1) : False := by
    apply freeOfWmax he hk hkval ht
    simp only [wmax, Finset.mem_filter, Finset.mem_univ, true_and]
    intro x hx xt
    exact joint x (andFromInputs hAO hl ho h0 h1 xt xt) hx
  obtain ⟨l,hl',el⟩ := junkInputHits hAO hT hs joint he hjval hkval 0
  obtain ⟨r,hr',er⟩ := junkInputHits hAO hT hs joint he hjval hkval 1
  have le : l ∈ exclusive (n := n) C j 0 :=
    Finset.mem_sdiff.mpr ⟨hl', fun h => disj el hl' h⟩
  have re : r ∈ exclusive (n := n) C j 1 :=
    Finset.mem_sdiff.mpr ⟨hr', fun h => disj er h hr'⟩
  rcases el with rfl | rfl <;> rcases er with rfl | rfl
  · exact (disj (.inl rfl) hl' hr').elim
  · exact .inl ⟨le,re⟩
  · exact .inr ⟨le,re⟩
  · exact (disj (.inr rfl) hl' hr').elim


lemma uniqueCenter (h4 : NoFourCycle G) {X : Finset (Fin n)} {a b : Fin n}
    (hX : 1 < X.card) (ha : ∀ x ∈ X, G.Adj a x) (hb : ∀ x ∈ X, G.Adj b x) :
    a = b := by
  by_contra ne
  have hsub : X ⊆ Finset.univ.filter (fun w => G.Adj a w ∧ G.Adj b w) := by
    intro x hx
    simp [ha x hx, hb x hx]
  exact (Nat.not_le_of_lt hX) ((Finset.card_le_card hsub).trans (h4 a b ne))

lemma orInRaw {w : ℕ} (h : w < n) :
    orIn n C w = {⟨w,h⟩} := by
  ext x
  constructor
  · intro hx
    rcases Relation.ReflTransGen.cases_head (mem_orIn_reach x hx) with he | ⟨z,hz,_⟩
    · exact Finset.mem_singleton.mpr (Fin.ext he.symm)
    · obtain ⟨k,_,eq,_,_,_⟩ := hz
      omega
  · intro hx
    obtain rfl := Finset.mem_singleton.mp hx
    exact reach_mem_orIn _ Relation.ReflTransGen.refl

lemma orInAnd {j : ℕ} (hop : (gateAt C j).op = GateOp.and) :
    orIn n C (n + j) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  rcases Relation.ReflTransGen.cases_head (mem_orIn_reach x hx) with he | ⟨z, hs, _⟩
  · have := x.isLt
    omega
  · obtain ⟨k, _, he, hk, _, _⟩ := hs
    have e : k = j := by omega
    subst k
    rw [hop] at hk
    contradiction

-- Stop following an OR path as soon as its support contains at most one leaf.
def RelevantStep (n : ℕ) (C : Circuit) (X : Finset (Fin n)) (p q : ℕ) : Prop :=
  OrStep n C p q ∧ 1 < (orIn n C p ∩ X).card

def RelevantReach (n : ℕ) (C : Circuit) (X : Finset (Fin n)) :=
  Relation.ReflTransGen (RelevantStep n C X)

lemma relevantImpliesOr {X : Finset (Fin n)} {w z : ℕ}
    (h : RelevantReach n C X w z) : Relation.ReflTransGen (OrStep n C) w z := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact ih.tail step.1

noncomputable def relevantCone (n : ℕ) (C : Circuit) (X : Finset (Fin n)) (w : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (w+1)).filter (RelevantReach n C X w)

lemma relevantMem {X : Finset (Fin n)} {w z : ℕ} :
    z ∈ relevantCone n C X w ↔ RelevantReach n C X w z := by
  classical
  simp only [relevantCone,Finset.mem_filter,Finset.mem_range]
  exact ⟨And.right,fun h => ⟨Nat.lt_succ_of_le (orStep_le (relevantImpliesOr h)),h⟩⟩

lemma relevantBoundary {X : Finset (Fin n)} {w : ℕ} {x : Fin n}
    (path : Relation.ReflTransGen (OrStep n C) w x.val) :
    ∃ z, RelevantReach n C X w z ∧ (orIn n C z ∩ X).card ≤ 1 ∧ x ∈ orIn n C z := by
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl =>
    refine ⟨x.val,Relation.ReflTransGen.refl, ?_,reach_mem_orIn x Relation.ReflTransGen.refl⟩
    rw [orInRaw x.isLt]
    exact (Finset.card_le_card Finset.inter_subset_left).trans_eq (Finset.card_singleton _)
  | @head a b step path ih =>
    by_cases many : 1 < (orIn n C a ∩ X).card
    · obtain ⟨z,hz,few,mem⟩ := ih
      exact ⟨z,hz.head ⟨step,many⟩,few,mem⟩
    · exact ⟨a,Relation.ReflTransGen.refl,by omega,reach_mem_orIn x (path.head step)⟩

lemma starLeafBudget (hAO : IsAO2 n C) (h4 : NoFourCycle G)
    {c : Fin n} {X : Finset (Fin n)} {w : ℕ} (hw : w < n + C.gates.length)
    (hX : X ⊆ orIn n C w) (hedge : ∀ x ∈ X, s(c,x) ∈ Ustar G C) :
    ∃ P ⊆ orN G C \ lam G C, X.card ≤ P.card + 1 ∧
      ∀ i ∈ P, Relation.ReflTransGen (OrStep n C) w (n+i) ∧
        (orIn n C (n+i) ∩ X).Nonempty := by
  classical
  let cone := relevantCone n C X w
  let big (z : ℕ) := 1 < (orIn n C z ∩ X).card
  let internal := cone.filter big
  let frontier := cone \ internal
  have rootIncluded : ({w} : Finset ℕ) ⊆ cone := by
    intro z hz
    obtain rfl := Finset.mem_singleton.mp hz
    exact relevantMem.mpr .refl
  have internalIncluded : internal ⊆ cone := Finset.filter_subset _ _
  have childCoverage :
      cone \ {w} ⊆ internal.biUnion (fun z => {opnd C (z-n) 0, opnd C (z-n) 1}) := by
    intro y hy
    obtain ⟨cy, notRoot⟩ := Finset.mem_sdiff.mp hy
    rcases Relation.ReflTransGen.cases_tail (relevantMem.mp cy) with same | ⟨z,reach,last⟩
    · exact (notRoot (by simp [same])).elim
    · obtain ⟨i,hi,eq,_,input,_⟩ := last.1
      have zm : z ∈ internal := Finset.mem_filter.mpr ⟨relevantMem.mpr reach,last.2⟩
      refine Finset.mem_biUnion.mpr ⟨z,zm,?_⟩
      obtain ⟨b,hb⟩ := inputsAsOpnd hAO hi input
      have ezi : z - n = i := by omega
      rw [ezi,hb]
      fin_cases b <;> simp
  have branchCount : (internal.biUnion (fun z => {opnd C (z-n) 0, opnd C (z-n) 1})).card ≤
      2 * internal.card := by
    refine Finset.card_biUnion_le.trans ?_
    have sum := Finset.sum_le_sum (s := internal) (fun v (_ : v ∈ internal) =>
      (Finset.card_insert_le (opnd C (v-n) 0) {opnd C (v-n) 1}).trans_eq
        (by simp : ({opnd C (v-n) 1} : Finset ℕ).card + 1 = 2))
    simpa [Nat.mul_comm] using sum
  have frontierCard : frontier.card ≤ internal.card + 1 := by
    have h0 := (Finset.card_le_card childCoverage).trans branchCount
    have h1 := Finset.card_sdiff_add_card_eq_card rootIncluded
    have h2 := Finset.card_sdiff_add_card_eq_card internalIncluded
    rw [Finset.card_singleton] at h1
    change (cone \ internal).card ≤ internal.card + 1
    omega
  have traceWire (z : ℕ) (hz : z ∈ internal) :
      Relation.ReflTransGen (OrStep n C) w z :=
    relevantImpliesOr (relevantMem.mp (Finset.mem_filter.mp hz).1)
  have nle (z : ℕ) (hz : z ∈ internal) : n ≤ z := by
    by_contra! small
    have h := (Finset.mem_filter.mp hz).2
    change 1 < (orIn n C z ∩ X).card at h
    rw [orInRaw small] at h
    have le := Finset.card_le_card (Finset.inter_subset_left :
      ({⟨z,small⟩} : Finset (Fin n)) ∩ X ⊆ {⟨z,small⟩})
    rw [Finset.card_singleton] at le
    omega
  let P := internal.image (fun z => z-n)
  have iCount : P.card = internal.card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy e
    have xN := nle x hx
    have yN := nle y hy
    change x-n = y-n at e
    omega
  have subP : P ⊆ orN G C \ lam G C := by
    intro k hk
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hk
    have nz := nle z hz
    have eq : n+(z-n)=z := by omega
    have below := orStep_le (traceWire z hz)
    have hkl : z-n < C.gates.length := by omega
    have bigZ : 1 < (orIn n C (n+(z-n)) ∩ X).card := by
      rw [eq]
      exact (Finset.mem_filter.mp hz).2
    have hop : (gateAt C (z-n)).op = GateOp.or := by
      rcases hAO.1 _ (gateAt_mem hkl) with hand | hor
      · rw [orInAnd hand, Finset.empty_inter, Finset.card_empty] at bigZ
        omega
      · exact hor
    have existsLeaf := Finset.card_pos.mp (by omega : 0 < (orIn n C (n+(z-n)) ∩ X).card)
    obtain ⟨x,hx⟩ := existsLeaf
    refine Finset.mem_sdiff.mpr ⟨orNOfRaw hkl hop ⟨x,(Finset.mem_inter.mp hx).1⟩, ?_⟩
    intro hlam
    obtain ⟨t,ht⟩ := lamAvoidsUstar hlam (fun a ha u hu v hv => topAdj hAO ha hu hv)
    have et : t = c := uniqueCenter h4 bigZ (fun y hy => (ht y (Finset.mem_inter.mp hy).1).1)
      (fun y hy => SimpleGraph.mem_edgeFinset.mp
        (Finset.mem_sdiff.mp (hedge y (Finset.mem_inter.mp hy).2)).1)
    subst t
    exact (ht x (Finset.mem_inter.mp hx).1).2 (hedge x (Finset.mem_inter.mp hx).2)
  have trace (k : ℕ) (hk : k ∈ P) :
      Relation.ReflTransGen (OrStep n C) w (n+k) ∧ (orIn n C (n+k) ∩ X).Nonempty := by
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hk
    have hn := nle z hz
    have eq : n+(z-n)=z := by omega
    rw [eq]
    have hz' : 1 < (orIn n C z ∩ X).card := (Finset.mem_filter.mp hz).2
    exact ⟨traceWire z hz, Finset.card_pos.mp (by omega)⟩
  let leaves (z : ℕ) := orIn n C z ∩ X
  have coverage : X ⊆ frontier.biUnion leaves := by
    intro x hx
    obtain ⟨z,zr,small,xz⟩ := relevantBoundary (X := X) (mem_orIn_reach x (hX hx))
    refine Finset.mem_biUnion.mpr ⟨z, ?_, Finset.mem_inter.mpr ⟨xz,hx⟩⟩
    have mz : z ∈ cone := relevantMem.mpr zr
    exact Finset.mem_sdiff.mpr ⟨mz,
      fun bad => (Nat.not_le_of_lt (Finset.mem_filter.mp bad).2) small⟩
  have leafOne : ∀ z ∈ frontier, (leaves z).card ≤ 1 := by
    intro z hz
    obtain ⟨atCone,notInt⟩ := Finset.mem_sdiff.mp hz
    exact Nat.le_of_not_gt (fun h => notInt (Finset.mem_filter.mpr ⟨atCone,h⟩))
  refine ⟨P,subP,?_,trace⟩
  calc
    X.card ≤ (frontier.biUnion leaves).card := Finset.card_le_card coverage
    _ ≤ ∑ v ∈ frontier, (leaves v).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ frontier, (1 : ℕ) := Finset.sum_le_sum leafOne
    _ = frontier.card := by simp
    _ ≤ internal.card + 1 := frontierCard
    _ = P.card + 1 := by rw [iCount]


def crossBlock (A B : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  (A ×ˢ B).image fun p => s(p.1,p.2)

lemma crossBlock_comm (A B : Finset (Fin n)) : crossBlock A B = crossBlock B A := by
  ext e
  constructor <;> intro he
  all_goals
    obtain ⟨⟨u,v⟩,h,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hu,hv⟩ := Finset.mem_product.mp h
    exact Finset.mem_image.mpr ⟨(v,u), Finset.mem_product.mpr ⟨hv,hu⟩, Sym2.eq_swap⟩

lemma starFromSingleton {A B : Finset (Fin n)} {E : Finset (Sym2 (Fin n))}
    (hE : E ⊆ crossBlock A B) (hne : E.Nonempty) (hB : B.card ≤ 1) :
    ∃ c : Fin n, ∃ X ⊆ A, E.card ≤ X.card ∧ ∀ x ∈ X, s(c,x) ∈ E := by
  classical
  obtain ⟨e,he⟩ := hne
  obtain ⟨⟨u,c⟩,huv,_⟩ := Finset.mem_image.mp (hE he)
  have hc := (Finset.mem_product.mp huv).2
  let X := A.filter fun x => s(c,x) ∈ E
  have hSub : E ⊆ X.image (fun x => s(c,x)) := by
    intro f hf
    obtain ⟨⟨x,d⟩,hxd,rfl⟩ := Finset.mem_image.mp (hE hf)
    obtain ⟨hx,hd⟩ := Finset.mem_product.mp hxd
    have eq := Finset.card_le_one.mp hB d hd c hc
    change d = c at eq
    subst d
    rw [Sym2.eq_swap] at hf
    exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx,hf⟩, Sym2.eq_swap⟩
  exact ⟨c, X, Finset.filter_subset _ _, (Finset.card_le_card hSub).trans
    Finset.card_image_le, fun x hx => (Finset.mem_filter.mp hx).2⟩

lemma blockStar (h4 : NoFourCycle G) {A B : Finset (Fin n)} {E : Finset (Sym2 (Fin n))}
    (hE : E ⊆ crossBlock A B) (hne : E.Nonempty)
    (adj : ∀ u ∈ A, ∀ v ∈ B, G.Adj u v) :
    (∃ c : Fin n, ∃ X ⊆ A, E.card ≤ X.card ∧ ∀ x ∈ X, s(c,x) ∈ E) ∨
    (∃ c : Fin n, ∃ X ⊆ B, E.card ≤ X.card ∧ ∀ x ∈ X, s(c,x) ∈ E) := by
  by_cases hB : B.card ≤ 1
  · exact .inl (starFromSingleton hE hne hB)
  · have hA : A.card ≤ 1 := by
      by_contra! h
      obtain ⟨a,ha,b,hb,ne⟩ := Finset.one_lt_card.mp h
      exact ne (uniqueCenter h4 (Nat.lt_of_not_ge hB) (adj a ha) (adj b hb))
    exact .inr (starFromSingleton (crossBlock_comm A B ▸ hE) hne hA)

lemma twoStarsOnOppositeSides (hAO : IsAO2 n C) (h4 : NoFourCycle G)
    {a : ℕ} (ha : a < C.gates.length)
    {b d : Fin 2} (hne : b ≠ d)
    {c f : Fin n} {X Y : Finset (Fin n)}
    (hX : X ⊆ exclusive (n := n) C a b)
    (hY : Y ⊆ exclusive (n := n) C a d)
    (ex : ∀ x ∈ X, s(c,x) ∈ Ustar G C)
    (ey : ∀ y ∈ Y, s(f,y) ∈ Ustar G C) :
    X.card + Y.card ≤ 2 + (orN G C \ lam G C).card := by
  have hx : X ⊆ side (n := n) C a b := fun _ h => (Finset.mem_sdiff.mp (hX h)).1
  have hy : Y ⊆ side (n := n) C a d := fun _ h => (Finset.mem_sdiff.mp (hY h)).1
  have bound (i : Fin 2) : opnd C a i < n + C.gates.length :=
    (opndBound hAO ha i).trans (by omega)
  obtain ⟨P,hP,pn,pt⟩ := starLeafBudget hAO h4 (bound b) hx ex
  obtain ⟨Q,hQ,qn,qt⟩ := starLeafBudget hAO h4 (bound d) hy ey
  have ed : d = 1-b := (eitherOperand b d).resolve_left (Ne.symm hne)
  have hpq : Disjoint P Q := by
    apply Finset.disjoint_left.mpr
    intro i hiP hiQ
    obtain ⟨x,hx⟩ := (pt i hiP).2
    obtain ⟨hin,hx⟩ := Finset.mem_inter.mp hx
    have hm : x ∈ side (n := n) C a d := orInTrans (qt i hiQ).1 hin
    exact exclusiveDisjoint (hX hx) (ed ▸ hm)
  have cards := Finset.card_le_card (Finset.union_subset hP hQ)
  rw [Finset.card_union_of_disjoint hpq] at cards
  omega

lemma oppositeAddOne (b : Fin 2) : b + 1 = 1 - b := by
  fin_cases b <;> decide

lemma residualBound (h4 : NoFourCycle G) (hL : IsLeastAO G C) (hT : TopForm G C)
    (hTwo : (junk G C).card = 2) :
    (Ustar G C \ coveredByJunk G C).card ≤ 2 + (orN G C \ lam G C).card := by
  classical
  let R := Ustar G C \ coveredByJunk G C
  change R.card ≤ _
  by_cases hR : R.Nonempty
  · obtain ⟨j,k,_,hs⟩ := Finset.card_eq_two.mp hTwo
    have hj : j ∈ junk G C := by simp [hs]
    have hk : k ∈ junk G C := by simp [hs]
    have sk : junk G C = {k,j} := hs.trans (Finset.pair_comm _ _)
    obtain ⟨edge,he⟩ := hR
    induction edge using Sym2.ind with
    | h u v =>
      have joint := (residualJoint hL hT hs he).1
      let A (r : Fin 2) := exclusive (n := n) C j 0 ∩ exclusive (n := n) C k r
      let B (r : Fin 2) := exclusive (n := n) C j 1 ∩ exclusive (n := n) C k (1-r)
      let E (r : Fin 2) := R ∩ crossBlock (A r) (B r)
      have adj (r : Fin 2) (x : Fin n) (hx : x ∈ A r) (y : Fin n) (hy : y ∈ B r) :
          G.Adj x y := by
        have jx := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hx).1).1
        have jy := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hy).1).1
        have kx := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hx).2).1
        have ky := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hy).2).1
        obtain ⟨jl,jo,_⟩ := junkData hj
        obtain ⟨kl,ko,_⟩ := junkData hk
        apply (graphFun_pair G x y).mp
        apply joint
        · exact andFromInputs hL.1 jl jo jx jy (pairInput_left x y) (pairInput_right x y)
        · fin_cases r
          · exact andFromInputs hL.1 kl ko kx ky (pairInput_left x y) (pairInput_right x y)
          · exact andFromInputs hL.1 kl ko ky kx (pairInput_right x y) (pairInput_left x y)
      have star (r : Fin 2) : ∃ (b : Fin 2) (c : Fin n) (X : Finset (Fin n)),
          X ⊆ exclusive (n := n) C j b ∩ exclusive (n := n) C k (r+b) ∧
          (E r).card ≤ X.card ∧ ∀ x ∈ X, s(c,x) ∈ Ustar G C := by
        by_cases hn : (E r).Nonempty
        · rcases blockStar h4 (E := E r) Finset.inter_subset_right hn (adj r) with
            ⟨c,X,hX,hc,h⟩ | ⟨c,X,hX,hc,h⟩
          · exact ⟨0,c,X,by simpa [A] using hX,hc,
              fun x hx => (Finset.mem_sdiff.mp (Finset.mem_inter.mp (h x hx)).1).1⟩
          · exact ⟨1,c,X,by simpa [B, oppositeAddOne] using hX,hc,
              fun x hx => (Finset.mem_sdiff.mp (Finset.mem_inter.mp (h x hx)).1).1⟩
        · rw [Finset.not_nonempty_iff_eq_empty.mp hn]
          exact ⟨0,u,∅,by simp,by simp,by simp⟩
      have cover : R ⊆ E 0 ∪ E 1 := by
        intro e h
        induction e using Sym2.ind with
        | h x y =>
          obtain ⟨joint,hjv,hkv⟩ := residualJoint hL hT hs h
          have hL' := junkOrientation hL.1 hT hs joint h hjv hkv
          have hR' := junkOrientation hL.1 hT sk (joint_comm joint) h hkv hjv
          have put (p q : Fin n) (r : Fin 2) (hp : p ∈ A r) (hq : q ∈ B r)
              (eq : s(p,q) = s(x,y)) : s(x,y) ∈ E r :=
            Finset.mem_inter.mpr ⟨h, Finset.mem_image.mpr
              ⟨(p,q),Finset.mem_product.mpr ⟨hp,hq⟩,eq⟩⟩
          apply Finset.mem_union.mpr
          rcases hL' with ⟨l,r⟩ | ⟨l,r⟩ <;> rcases hR' with ⟨l',r'⟩ | ⟨l',r'⟩
          · exact .inl (put x y 0 (Finset.mem_inter.mpr ⟨l,l'⟩)
              (Finset.mem_inter.mpr ⟨r,r'⟩) rfl)
          · exact .inr (put x y 1 (Finset.mem_inter.mpr ⟨l,r'⟩)
              (Finset.mem_inter.mpr ⟨r,l'⟩) rfl)
          · exact .inr (put y x 1 (Finset.mem_inter.mpr ⟨l,r'⟩)
              (Finset.mem_inter.mpr ⟨r,l'⟩) Sym2.eq_swap)
          · exact .inl (put y x 0 (Finset.mem_inter.mpr ⟨l,l'⟩)
              (Finset.mem_inter.mpr ⟨r,r'⟩) Sym2.eq_swap)
      obtain ⟨b,c,X,hX,xn,hxe⟩ := star 0
      obtain ⟨d,f,Y,hY,yn,hye⟩ := star 1
      have budget : X.card + Y.card ≤ 2 + (orN G C \ lam G C).card := by
        by_cases e : b = d
        · subst d
          have hn : (0 : Fin 2) + b ≠ 1 + b := by fin_cases b <;> decide
          exact twoStarsOnOppositeSides hL.1 h4 (junkData hk).1 hn
            (fun _ hx => (Finset.mem_inter.mp (hX hx)).2)
            (fun _ hy => (Finset.mem_inter.mp (hY hy)).2) hxe hye
        · exact twoStarsOnOppositeSides hL.1 h4 (junkData hj).1 e
            (fun _ hx => (Finset.mem_inter.mp (hX hx)).1)
            (fun _ hy => (Finset.mem_inter.mp (hY hy)).1) hxe hye
      have hcard := (Finset.card_le_card cover).trans (Finset.card_union_le (E 0) (E 1))
      omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp hR, Finset.card_empty]
    exact Nat.zero_le _


lemma coveredByJunk_empty (hw : ∀ j ∈ junk G C, wmax G C j = ∅) :
    coveredByJunk G C = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨j, hj, he⟩ := Finset.mem_biUnion.mp he
  have hd := (Finset.mem_filter.mp he).2
  rw [hw j hj] at hd
  exact hd (Finset.disjoint_empty_right _)

lemma wmax_empty_residual_bound (h4 : NoFourCycle G) (hL : IsLeastAO G C)
    (hT : TopForm G C) (hTwo : (junk G C).card = 2)
    (hw : ∀ j ∈ junk G C, wmax G C j = ∅) :
    (Ustar G C).card ≤ 2 + (orN G C \ lam G C).card := by
  have h := residualBound h4 hL hT hTwo
  rw [coveredByJunk_empty hw, Finset.sdiff_empty] at h
  exact h

lemma leafBudget (hAO : IsAO2 n C)
    {X : Finset (Fin n)} {w : ℕ} (hw : w < n + C.gates.length)
    (hX : X ⊆ orIn n C w)
    (hfree : ∀ k, k < C.gates.length → 1 < (orIn n C (n+k) ∩ X).card → k ∉ lam G C) :
    ∃ P ⊆ orN G C \ lam G C, X.card ≤ P.card + 1 ∧
      ∀ i ∈ P, Relation.ReflTransGen (OrStep n C) w (n+i) ∧
        1 < (orIn n C (n+i) ∩ X).card := by
  classical
  let cone := relevantCone n C X w
  let big (z : ℕ) := 1 < (orIn n C z ∩ X).card
  let internal := cone.filter big
  let frontier := cone \ internal
  have rootIncluded : ({w} : Finset ℕ) ⊆ cone := by
    intro z hz
    obtain rfl := Finset.mem_singleton.mp hz
    exact relevantMem.mpr .refl
  have internalIncluded : internal ⊆ cone := Finset.filter_subset _ _
  have childCoverage :
      cone \ {w} ⊆ internal.biUnion (fun z => {opnd C (z-n) 0, opnd C (z-n) 1}) := by
    intro y hy
    obtain ⟨cy, notRoot⟩ := Finset.mem_sdiff.mp hy
    rcases Relation.ReflTransGen.cases_tail (relevantMem.mp cy) with same | ⟨z,reach,last⟩
    · exact (notRoot (by simp [same])).elim
    · obtain ⟨i,hi,eq,_,input,_⟩ := last.1
      have zm : z ∈ internal := Finset.mem_filter.mpr ⟨relevantMem.mpr reach,last.2⟩
      refine Finset.mem_biUnion.mpr ⟨z,zm,?_⟩
      obtain ⟨b,hb⟩ := inputsAsOpnd hAO hi input
      have ezi : z - n = i := by omega
      rw [ezi,hb]
      fin_cases b <;> simp
  have branchCount : (internal.biUnion (fun z => {opnd C (z-n) 0, opnd C (z-n) 1})).card ≤
      2 * internal.card := by
    refine Finset.card_biUnion_le.trans ?_
    have sum := Finset.sum_le_sum (s := internal) (fun v (_ : v ∈ internal) =>
      (Finset.card_insert_le (opnd C (v-n) 0) {opnd C (v-n) 1}).trans_eq
        (by simp : ({opnd C (v-n) 1} : Finset ℕ).card + 1 = 2))
    simpa [Nat.mul_comm] using sum
  have frontierCard : frontier.card ≤ internal.card + 1 := by
    have h0 := (Finset.card_le_card childCoverage).trans branchCount
    have h1 := Finset.card_sdiff_add_card_eq_card rootIncluded
    have h2 := Finset.card_sdiff_add_card_eq_card internalIncluded
    rw [Finset.card_singleton] at h1
    change (cone \ internal).card ≤ internal.card + 1
    omega
  have traceWire (z : ℕ) (hz : z ∈ internal) :
      Relation.ReflTransGen (OrStep n C) w z :=
    relevantImpliesOr (relevantMem.mp (Finset.mem_filter.mp hz).1)
  have nle (z : ℕ) (hz : z ∈ internal) : n ≤ z := by
    by_contra! small
    have h := (Finset.mem_filter.mp hz).2
    change 1 < (orIn n C z ∩ X).card at h
    rw [orInRaw small] at h
    have le := Finset.card_le_card (Finset.inter_subset_left :
      ({⟨z,small⟩} : Finset (Fin n)) ∩ X ⊆ {⟨z,small⟩})
    rw [Finset.card_singleton] at le
    omega
  let P := internal.image (fun z => z-n)
  have iCount : P.card = internal.card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy e
    have xN := nle x hx
    have yN := nle y hy
    change x-n = y-n at e
    omega
  have subP : P ⊆ orN G C \ lam G C := by
    intro k hk
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hk
    have nz := nle z hz
    have eq : n+(z-n)=z := by omega
    have below := orStep_le (traceWire z hz)
    have hkl : z-n < C.gates.length := by omega
    have bigZ : 1 < (orIn n C (n+(z-n)) ∩ X).card := by
      rw [eq]
      exact (Finset.mem_filter.mp hz).2
    have hop : (gateAt C (z-n)).op = GateOp.or := by
      rcases hAO.1 _ (gateAt_mem hkl) with hand | hor
      · rw [orInAnd hand, Finset.empty_inter, Finset.card_empty] at bigZ
        omega
      · exact hor
    have existsLeaf := Finset.card_pos.mp (by omega : 0 < (orIn n C (n+(z-n)) ∩ X).card)
    obtain ⟨x,hx⟩ := existsLeaf
    refine Finset.mem_sdiff.mpr ⟨orNOfRaw hkl hop ⟨x,(Finset.mem_inter.mp hx).1⟩, ?_⟩
    exact hfree (z-n) hkl bigZ
  have trace (k : ℕ) (hk : k ∈ P) :
      Relation.ReflTransGen (OrStep n C) w (n+k) ∧ 1 < (orIn n C (n+k) ∩ X).card := by
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hk
    have hn := nle z hz
    have eq : n+(z-n)=z := by omega
    rw [eq]
    have hz' : 1 < (orIn n C z ∩ X).card := (Finset.mem_filter.mp hz).2
    exact ⟨traceWire z hz, hz'⟩
  let leaves (z : ℕ) := orIn n C z ∩ X
  have coverage : X ⊆ frontier.biUnion leaves := by
    intro x hx
    obtain ⟨z,zr,small,xz⟩ := relevantBoundary (X := X) (mem_orIn_reach x (hX hx))
    refine Finset.mem_biUnion.mpr ⟨z, ?_, Finset.mem_inter.mpr ⟨xz,hx⟩⟩
    have mz : z ∈ cone := relevantMem.mpr zr
    exact Finset.mem_sdiff.mpr ⟨mz,
      fun bad => (Nat.not_le_of_lt (Finset.mem_filter.mp bad).2) small⟩
  have leafOne : ∀ z ∈ frontier, (leaves z).card ≤ 1 := by
    intro z hz
    obtain ⟨atCone,notInt⟩ := Finset.mem_sdiff.mp hz
    exact Nat.le_of_not_gt (fun h => notInt (Finset.mem_filter.mpr ⟨atCone,h⟩))
  refine ⟨P,subP,?_,trace⟩
  calc
    X.card ≤ (frontier.biUnion leaves).card := Finset.card_le_card coverage
    _ ≤ ∑ v ∈ frontier, (leaves v).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ frontier, (1 : ℕ) := Finset.sum_le_sum leafOne
    _ = frontier.card := by simp
    _ ≤ internal.card + 1 := frontierCard
    _ = P.card + 1 := by rw [iCount]


lemma lam_same_color (hAO : IsAO2 n C) (s : Fin n → Bool)
    (hs : ∀ u v, G.Adj u v → s u ≠ s v) {k : ℕ} (hk : k ∈ lam G C)
    {a b : Fin n} (ha : a ∈ orIn n C (n+k)) (hb : b ∈ orIn n C (n+k)) : s a = s b := by
  obtain ⟨t, ht⟩ := lamAvoidsUstar hk (fun j hj u hu v hv => topAdj hAO hj hu hv)
  have hta := hs t a (ht a ha).1
  have htb := hs t b (ht b hb).1
  cases hs0 : s t <;> cases hs1 : s a <;> cases hs2 : s b <;> simp_all

lemma star_pair_not_lam (hAO : IsAO2 n C) (h4 : NoFourCycle G)
    {c a b : Fin n} (hab : a ≠ b)
    (hae : s(c,a) ∈ Ustar G C) (hbe : s(c,b) ∈ Ustar G C)
    {k : ℕ} (ha : a ∈ orIn n C (n+k)) (hb : b ∈ orIn n C (n+k)) : k ∉ lam G C := by
  intro hk
  obtain ⟨t, ht⟩ := lamAvoidsUstar hk (fun j hj u hu v hv => topAdj hAO hj hu hv)
  have hp : 1 < ({a,b} : Finset (Fin n)).card := by simp [hab]
  have etc : t = c := uniqueCenter h4 hp
    (by
      intro x hx
      have hx' : x = a ∨ x = b := by simpa only [Finset.mem_insert, Finset.mem_singleton] using hx
      rcases hx' with hx' | hx'
      · exact hx' ▸ (ht a ha).1
      · exact hx' ▸ (ht b hb).1)
    (by intro x hx; rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hx : x = a ∨ x = b) with rfl | rfl
        exact SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp hae).1
        exact SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp hbe).1)
  subst t
  exact (ht a ha).2 hae

lemma anchored_star_free (hAO : IsAO2 n C) (h4 : NoFourCycle G)
    (s : Fin n → Bool) (hs : ∀ u v, G.Adj u v → s u ≠ s v)
    {c z : Fin n} {X : Finset (Fin n)}
    (hedge : ∀ x ∈ X, s(c,x) ∈ Ustar G C)
    (hcolor : ∀ x ∈ X, s x ≠ s z)
    (k : ℕ) (hbig : 1 < (orIn n C (n+k) ∩ insert z X).card) : k ∉ lam G C := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hbig
  obtain ⟨hIa, hXa⟩ := Finset.mem_inter.mp ha
  obtain ⟨hIb, hXb⟩ := Finset.mem_inter.mp hb
  rcases Finset.mem_insert.mp hXa with haz | hXa
  · rcases Finset.mem_insert.mp hXb with hbz | hXb
    · exact (hab (haz.trans hbz.symm)).elim
    · intro hk
      have he := lam_same_color hAO s hs hk hIb hIa
      exact hcolor b hXb (he.trans (congrArg s haz))
  · rcases Finset.mem_insert.mp hXb with hbz | hXb
    · intro hk
      have he := lam_same_color hAO s hs hk hIa hIb
      exact hcolor a hXa (he.trans (congrArg s hbz))
    · exact star_pair_not_lam hAO h4 hab (hedge a hXa) (hedge b hXb) hIa hIb

lemma insert_big_has_leaf {X : Finset (Fin n)} {z : Fin n} {S : Finset (Fin n)}
    (hbig : 1 < (S ∩ insert z X).card) : (S ∩ X).Nonempty := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hbig
  obtain ⟨hIa, hXa⟩ := Finset.mem_inter.mp ha
  obtain ⟨hIb, hXb⟩ := Finset.mem_inter.mp hb
  rcases Finset.mem_insert.mp hXa with haz | hXa
  · rcases Finset.mem_insert.mp hXb with hbz | hXb
    · exact (hab (haz.trans hbz.symm)).elim
    · exact ⟨b, Finset.mem_inter.mpr ⟨hIb,hXb⟩⟩
  · exact ⟨a, Finset.mem_inter.mpr ⟨hIa,hXa⟩⟩

lemma anchored_star_budget (hAO : IsAO2 n C) (h4 : NoFourCycle G)
    (s : Fin n → Bool) (hs : ∀ u v, G.Adj u v → s u ≠ s v)
    {c z : Fin n} {X : Finset (Fin n)} {w : ℕ} (hw : w < n + C.gates.length)
    (hX : X ⊆ orIn n C w) (hz : z ∈ orIn n C w)
    (hedge : ∀ x ∈ X, s(c,x) ∈ Ustar G C)
    (hcolor : ∀ x ∈ X, s x ≠ s z) :
    ∃ P ⊆ orN G C \ lam G C, X.card ≤ P.card ∧
      ∀ i ∈ P, Relation.ReflTransGen (OrStep n C) w (n+i) ∧
        (orIn n C (n+i) ∩ X).Nonempty := by
  have hzX : z ∉ X := fun h => hcolor z h rfl
  obtain ⟨P,hP,hcount,htrace⟩ := leafBudget hAO hw
    (Finset.insert_subset hz hX)
    (fun k _ hbig => anchored_star_free hAO h4 s hs hedge hcolor k hbig)
  refine ⟨P,hP,?_,?_⟩
  · rw [Finset.card_insert_of_notMem hzX] at hcount
    omega
  · intro k hk
    exact ⟨(htrace k hk).1, insert_big_has_leaf (htrace k hk).2⟩

lemma anchored_opposite_sides_budget (hAO : IsAO2 n C) (h4 : NoFourCycle G)
    (s : Fin n → Bool) (hs : ∀ u v, G.Adj u v → s u ≠ s v)
    {a : ℕ} (ha : a < C.gates.length) {b d : Fin 2} (hbd : b ≠ d)
    {c f : Fin n} {X Y : Finset (Fin n)}
    (hX : X ⊆ exclusive (n := n) C a b) (hY : Y ⊆ exclusive (n := n) C a d)
    (hf : f ∈ side (n := n) C a b) (hc : c ∈ side (n := n) C a d)
    (hcf : s c = s f)
    (ex : ∀ x ∈ X, s(c,x) ∈ Ustar G C) (ey : ∀ y ∈ Y, s(f,y) ∈ Ustar G C) :
    X.card + Y.card ≤ (orN G C \ lam G C).card := by
  have hx : X ⊆ side (n := n) C a b := fun _ h => (Finset.mem_sdiff.mp (hX h)).1
  have hy : Y ⊆ side (n := n) C a d := fun _ h => (Finset.mem_sdiff.mp (hY h)).1
  have bound (i : Fin 2) : opnd C a i < n + C.gates.length :=
    (opndBound hAO ha i).trans (by omega)
  have hcolorX : ∀ x ∈ X, s x ≠ s f := by
    intro x hx
    have hc := hs c x (SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (ex x hx)).1)
    exact fun he => hc (hcf.trans he.symm)
  have hcolorY : ∀ y ∈ Y, s y ≠ s c := by
    intro y hy
    have hf := hs f y (SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (ey y hy)).1)
    exact fun he => hf (hcf.symm.trans he.symm)
  obtain ⟨P,hP,pn,pt⟩ := anchored_star_budget hAO h4 s hs (bound b) hx hf ex hcolorX
  obtain ⟨Q,hQ,qn,qt⟩ := anchored_star_budget hAO h4 s hs (bound d) hy hc ey hcolorY
  have ed : d = 1-b := (eitherOperand b d).resolve_left (Ne.symm hbd)
  have hpq : Disjoint P Q := by
    apply Finset.disjoint_left.mpr
    intro i hiP hiQ
    obtain ⟨x,hx⟩ := (pt i hiP).2
    obtain ⟨hin,hx⟩ := Finset.mem_inter.mp hx
    have hm : x ∈ side (n := n) C a d := orInTrans (qt i hiQ).1 hin
    exact exclusiveDisjoint (hX hx) (ed ▸ hm)
  have cards := Finset.card_le_card (Finset.union_subset hP hQ)
  rw [Finset.card_union_of_disjoint hpq] at cards
  omega

lemma two_stars_union_free (hAO : IsAO2 n C) (h4 : NoFourCycle G)
    (s : Fin n → Bool) (hs : ∀ u v, G.Adj u v → s u ≠ s v)
    {c f : Fin n} {X Y : Finset (Fin n)} (hcf : s c ≠ s f)
    (ex : ∀ x ∈ X, s(c,x) ∈ Ustar G C) (ey : ∀ y ∈ Y, s(f,y) ∈ Ustar G C)
    (k : ℕ) (hbig : 1 < (orIn n C (n+k) ∩ (X ∪ Y)).card) : k ∉ lam G C := by
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp hbig
  obtain ⟨ha,ha'⟩ := Finset.mem_inter.mp ha
  obtain ⟨hb,hb'⟩ := Finset.mem_inter.mp hb
  have mixed {x y : Fin n} (hx : x ∈ X) (hy : y ∈ Y)
      (hix : x ∈ orIn n C (n+k)) (hiy : y ∈ orIn n C (n+k)) : k ∉ lam G C := by
    intro hk
    have hcx := hs c x (SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (ex x hx)).1)
    have hfy := hs f y (SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (ey y hy)).1)
    have hxy := lam_same_color hAO s hs hk hix hiy
    cases hc : s c <;> cases hf : s f <;> cases hx' : s x <;> cases hy' : s y <;> simp_all
  rcases Finset.mem_union.mp ha' with ha' | ha' <;> rcases Finset.mem_union.mp hb' with hb' | hb'
  · exact star_pair_not_lam hAO h4 hab (ex a ha') (ex b hb') ha hb
  · exact mixed ha' hb' ha hb
  · exact mixed hb' ha' hb ha
  · exact star_pair_not_lam hAO h4 hab (ey a ha') (ey b hb') ha hb

lemma mixed_wire_gate (hAO : IsAO2 n C) (s : Fin n → Bool)
    (hs : ∀ u v, G.Adj u v → s u ≠ s v) {w : ℕ} (hw : w < n+C.gates.length)
    {c f : Fin n} (hc : c ∈ orIn n C w) (hf : f ∈ orIn n C w) (hcf : s c ≠ s f) :
    ∃ k ∈ orN G C \ lam G C, w = n+k := by
  have hn : n ≤ w := by
    by_contra! hlt
    rw [orInRaw hlt] at hc hf
    have ec := Finset.mem_singleton.mp hc
    have ef := Finset.mem_singleton.mp hf
    exact hcf (congrArg s (ec.trans ef.symm))
  let k := w-n
  have he : w=n+k := by dsimp [k]; omega
  have hk : k<C.gates.length := by omega
  have hop : (gateAt C k).op = GateOp.or := by
    rcases hAO.1 _ (gateAt_mem hk) with hand | hor
    · rw [he, orInAnd hand] at hc
      exact (Finset.notMem_empty c hc).elim
    · exact hor
  refine ⟨k, Finset.mem_sdiff.mpr ⟨orNOfRaw hk hop ?_, ?_⟩, he⟩
  · exact ⟨c, he ▸ hc⟩
  · intro hlam
    exact hcf (lam_same_color hAO s hs hlam (he ▸ hc) (he ▸ hf))

lemma opposite_color_same_side_budget (hAO : IsAO2 n C) (h4 : NoFourCycle G)
    (s : Fin n → Bool) (hs : ∀ u v, G.Adj u v → s u ≠ s v)
    {a : ℕ} (ha : a < C.gates.length) {b : Fin 2}
    {c f : Fin n} {X Y : Finset (Fin n)}
    (hX : X ⊆ exclusive (n := n) C a b) (hY : Y ⊆ exclusive (n := n) C a b)
    (hc : c ∈ side (n := n) C a (1-b)) (hf : f ∈ side (n := n) C a (1-b))
    (hcf : s c ≠ s f)
    (ex : ∀ x ∈ X, s(c,x) ∈ Ustar G C) (ey : ∀ y ∈ Y, s(f,y) ∈ Ustar G C) :
    X.card + Y.card ≤ (orN G C \ lam G C).card := by
  have hXY : X ∪ Y ⊆ exclusive (n := n) C a b := Finset.union_subset hX hY
  have hleaves : X ∪ Y ⊆ side (n := n) C a b := fun _ h => (Finset.mem_sdiff.mp (hXY h)).1
  have bound (i : Fin 2) : opnd C a i < n + C.gates.length :=
    (opndBound hAO ha i).trans (by omega)
  have hdisj : Disjoint X Y := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hcx := hs c x (SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (ex x hx)).1)
    have hfx := hs f x (SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (ey x hy)).1)
    cases hc : s c <;> cases hf : s f <;> cases hx' : s x <;> simp_all
  obtain ⟨P,hP,pn,pt⟩ := leafBudget hAO (bound b) hleaves
    (fun k _ hbig => two_stars_union_free hAO h4 s hs hcf ex ey k hbig)
  obtain ⟨k,hk,hkw⟩ := mixed_wire_gate hAO s hs (bound (1-b)) hc hf hcf
  have hkP : k ∉ P := by
    intro hkp
    have hbig := (pt k hkp).2
    obtain ⟨x,hx⟩ := Finset.card_pos.mp (by omega : 0 < (orIn n C (n+k) ∩ (X ∪ Y)).card)
    obtain ⟨hin,hx⟩ := Finset.mem_inter.mp hx
    have hother : x ∈ side (n := n) C a (1-b) := by
      change x ∈ orIn n C (opnd C a (1-b))
      rw [hkw]
      exact hin
    exact exclusiveDisjoint (hXY hx) hother
  have hsubset : insert k P ⊆ orN G C \ lam G C := Finset.insert_subset hk hP
  have hcard := Finset.card_le_card hsubset
  rw [Finset.card_insert_of_notMem hkP] at hcard
  rw [Finset.card_union_of_disjoint hdisj] at pn
  omega

lemma crossed_stars_budget (hAO : IsAO2 n C) (h4 : NoFourCycle G)
    (s : Fin n → Bool) (hs : ∀ u v, G.Adj u v → s u ≠ s v)
    {j k : ℕ} (hj : j < C.gates.length) (hk : k < C.gates.length)
    {b d : Fin 2} {c f : Fin n} {X Y : Finset (Fin n)}
    (hX : X ⊆ exclusive (n := n) C j b ∩ exclusive (n := n) C k b)
    (hY : Y ⊆ exclusive (n := n) C j d ∩ exclusive (n := n) C k (1+d))
    (hc : c ∈ exclusive (n := n) C j (1-b) ∩ exclusive (n := n) C k (1-b))
    (hf : f ∈ exclusive (n := n) C j (1-d) ∩ exclusive (n := n) C k d)
    (ex : ∀ x ∈ X, s(c,x) ∈ Ustar G C) (ey : ∀ y ∈ Y, s(f,y) ∈ Ustar G C) :
    X.card + Y.card ≤ (orN G C \ lam G C).card := by
  have jx : X ⊆ exclusive (n := n) C j b := fun x hx => (Finset.mem_inter.mp (hX hx)).1
  have jy : Y ⊆ exclusive (n := n) C j d := fun y hy => (Finset.mem_inter.mp (hY hy)).1
  have kx : X ⊆ exclusive (n := n) C k b := fun x hx => (Finset.mem_inter.mp (hX hx)).2
  have ky : Y ⊆ exclusive (n := n) C k (1+d) := fun y hy => (Finset.mem_inter.mp (hY hy)).2
  have jc : c ∈ side (n := n) C j (1-b) := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hc).1).1
  have kc : c ∈ side (n := n) C k (1-b) := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hc).2).1
  have jf : f ∈ side (n := n) C j (1-d) := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hf).1).1
  have kf : f ∈ side (n := n) C k d := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hf).2).1
  fin_cases b <;> fin_cases d
  all_goals norm_num at jx jy kx ky jc kc jf kf
  all_goals
    by_cases hcol : s c = s f
    · first
      | exact anchored_opposite_sides_budget hAO h4 s hs hj (by decide) jx jy jf jc hcol ex ey
      | exact anchored_opposite_sides_budget hAO h4 s hs hk (by decide) kx ky kf kc hcol ex ey
    · first
      | exact opposite_color_same_side_budget hAO h4 s hs hj jx jy jc jf hcol ex ey
      | exact opposite_color_same_side_budget hAO h4 s hs hk kx ky kc kf hcol ex ey

lemma starExtract {A B : Finset (Fin n)} {E : Finset (Sym2 (Fin n))}
    (hE : E ⊆ crossBlock A B) (hne : E.Nonempty) (hB : B.card ≤ 1) :
    ∃ c ∈ B, ∃ X ⊆ A, X.Nonempty ∧ E ⊆ X.image (fun x => s(c,x)) ∧
      ∀ x ∈ X, s(c,x) ∈ E := by
  classical
  obtain ⟨e,he⟩ := hne
  obtain ⟨⟨u,c⟩,huv,_⟩ := Finset.mem_image.mp (hE he)
  have hc := (Finset.mem_product.mp huv).2
  let X := A.filter fun x => s(c,x) ∈ E
  have hSub : E ⊆ X.image (fun x => s(c,x)) := by
    intro f hf
    obtain ⟨⟨x,d⟩,hxd,rfl⟩ := Finset.mem_image.mp (hE hf)
    obtain ⟨hx,hd⟩ := Finset.mem_product.mp hxd
    have eq := Finset.card_le_one.mp hB d hd c hc
    change d = c at eq
    subst d
    rw [Sym2.eq_swap] at hf
    exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx,hf⟩, Sym2.eq_swap⟩
  have hXne : X.Nonempty := by
    obtain ⟨x,hx,_⟩ := Finset.mem_image.mp (hSub he)
    exact ⟨x,hx⟩
  exact ⟨c,hc,X,Finset.filter_subset _ _,hXne,hSub,fun x hx => (Finset.mem_filter.mp hx).2⟩

lemma blockStarExtract (h4 : NoFourCycle G) {A B : Finset (Fin n)} {E : Finset (Sym2 (Fin n))}
    (hE : E ⊆ crossBlock A B) (hne : E.Nonempty)
    (adj : ∀ u ∈ A, ∀ v ∈ B, G.Adj u v) :
    (∃ c ∈ B, ∃ X ⊆ A, X.Nonempty ∧ E ⊆ X.image (fun x => s(c,x)) ∧ ∀ x ∈ X, s(c,x) ∈ E) ∨
    (∃ c ∈ A, ∃ X ⊆ B, X.Nonempty ∧ E ⊆ X.image (fun x => s(c,x)) ∧ ∀ x ∈ X, s(c,x) ∈ E) := by
  by_cases hB : B.card ≤ 1
  · exact .inl (starExtract hE hne hB)
  · have hA : A.card ≤ 1 := by
      by_contra! h
      obtain ⟨a,ha,b,hb,ne⟩ := Finset.one_lt_card.mp h
      exact ne (uniqueCenter h4 (Nat.lt_of_not_ge hB) (adj a ha) (adj b hb))
    exact .inr (starExtract (crossBlock_comm A B ▸ hE) hne hA)

lemma one_star_package {R : Finset (Sym2 (Fin n))} {c : Fin n} {X : Finset (Fin n)}
    {B : ℕ} (hX : X.Nonempty) (hcov : R ⊆ X.image (fun x => s(c,x)))
    (hedge : ∀ x ∈ X, G.Adj c x) (hcost : X.card+1 ≤ B) :
    ∃ (Z : Finset (Fin n)) (L : Fin n → Finset (Fin n)),
      (∀ v ∈ Z, (L v).Nonempty) ∧ (∀ v ∈ Z, ∀ u ∈ L v, G.Adj v u) ∧
      (∀ e ∈ R, ∃ v ∈ Z, ∃ u ∈ L v, e = s(v,u)) ∧
      (∑ v ∈ Z, (L v).card) + Z.card ≤ B := by
  refine ⟨{c},fun _ => X,?_,?_,?_,?_⟩
  · intro v hv; exact hX
  · intro v hv u hu
    obtain rfl := Finset.mem_singleton.mp hv
    exact hedge u hu
  · intro e he
    obtain ⟨x,hx,hxe⟩ := Finset.mem_image.mp (hcov he)
    exact ⟨c,by simp,x,hx,hxe.symm⟩
  · simpa using hcost

lemma two_star_package {R : Finset (Sym2 (Fin n))} {c f : Fin n} {X Y : Finset (Fin n)}
    {B : ℕ} (hX : X.Nonempty) (hY : Y.Nonempty)
    (hcov : R ⊆ X.image (fun x => s(c,x)) ∪ Y.image (fun y => s(f,y)))
    (ex : ∀ x ∈ X, G.Adj c x) (ey : ∀ y ∈ Y, G.Adj f y)
    (hcost : X.card+Y.card+2 ≤ B) :
    ∃ (Z : Finset (Fin n)) (L : Fin n → Finset (Fin n)),
      (∀ v ∈ Z, (L v).Nonempty) ∧ (∀ v ∈ Z, ∀ u ∈ L v, G.Adj v u) ∧
      (∀ e ∈ R, ∃ v ∈ Z, ∃ u ∈ L v, e = s(v,u)) ∧
      (∑ v ∈ Z, (L v).card) + Z.card ≤ B := by
  classical
  by_cases hcf : c = f
  · subst f
    apply one_star_package (X := X ∪ Y) (c := c) (hX.mono Finset.subset_union_left)
    · intro e he
      rcases Finset.mem_union.mp (hcov he) with he | he
      · obtain ⟨x,hx,hxe⟩ := Finset.mem_image.mp he
        exact Finset.mem_image.mpr ⟨x,Finset.mem_union_left Y hx,hxe⟩
      · obtain ⟨y,hy,hye⟩ := Finset.mem_image.mp he
        exact Finset.mem_image.mpr ⟨y,Finset.mem_union_right X hy,hye⟩
    · intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact ex x hx
      · exact ey x hx
    · have h := Finset.card_union_le X Y
      omega
  · refine ⟨{c,f},fun v => if v=c then X else Y,?_,?_,?_,?_⟩
    · intro v hv
      by_cases hvc : v=c
      · simpa [hvc] using hX
      · simpa [hvc] using hY
    · intro v hv u hu
      have hv' : v=c ∨ v=f := by simpa only [Finset.mem_insert,Finset.mem_singleton] using hv
      rcases hv' with rfl | rfl
      · exact ex u (by simpa using hu)
      · exact ey u (by simpa [Ne.symm hcf] using hu)
    · intro e he
      rcases Finset.mem_union.mp (hcov he) with he | he
      · obtain ⟨x,hx,hxe⟩ := Finset.mem_image.mp he
        exact ⟨c,by simp,x,by simpa using hx,hxe.symm⟩
      · obtain ⟨y,hy,hye⟩ := Finset.mem_image.mp he
        exact ⟨f,by simp,y,by simpa [Ne.symm hcf] using hy,hye.symm⟩
    · simpa [hcf,Ne.symm hcf] using hcost

lemma residual_star_cover (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v) (h4 : NoFourCycle G) (hL : IsLeastAO G C) (hT : TopForm G C)
    (hTwo : (junk G C).card = 2) :
    ∃ (Z : Finset (Fin n)) (L : Fin n → Finset (Fin n)),
      (∀ v ∈ Z, (L v).Nonempty) ∧ (∀ v ∈ Z, ∀ u ∈ L v, G.Adj v u) ∧
      (∀ e ∈ Ustar G C \ coveredByJunk G C, ∃ v ∈ Z, ∃ u ∈ L v, e = s(v,u)) ∧
      (∑ v ∈ Z, (L v).card) + Z.card ≤ (orN G C \ lam G C).card + 2 := by
  classical
  let R := Ustar G C \ coveredByJunk G C
  by_cases hR : R.Nonempty
  · obtain ⟨j,k,_,hs⟩ := Finset.card_eq_two.mp hTwo
    have hj : j ∈ junk G C := by simp [hs]
    have hk : k ∈ junk G C := by simp [hs]
    have sk : junk G C = {k,j} := hs.trans (Finset.pair_comm _ _)
    obtain ⟨edge,he⟩ := hR
    induction edge using Sym2.ind with
    | h u v =>
      have joint := (residualJoint hL hT hs he).1
      let A (r : Fin 2) := exclusive (n := n) C j 0 ∩ exclusive (n := n) C k r
      let B (r : Fin 2) := exclusive (n := n) C j 1 ∩ exclusive (n := n) C k (1-r)
      let E (r : Fin 2) := R ∩ crossBlock (A r) (B r)
      have adj (r : Fin 2) (x : Fin n) (hx : x ∈ A r) (y : Fin n) (hy : y ∈ B r) :
          G.Adj x y := by
        have jx := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hx).1).1
        have jy := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hy).1).1
        have kx := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hx).2).1
        have ky := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hy).2).1
        obtain ⟨jl,jo,_⟩ := junkData hj
        obtain ⟨kl,ko,_⟩ := junkData hk
        apply (graphFun_pair G x y).mp
        apply joint
        · exact andFromInputs hL.1 jl jo jx jy (pairInput_left x y) (pairInput_right x y)
        · fin_cases r
          · exact andFromInputs hL.1 kl ko kx ky (pairInput_left x y) (pairInput_right x y)
          · exact andFromInputs hL.1 kl ko ky kx (pairInput_right x y) (pairInput_left x y)
      have star (r : Fin 2) (hn : (E r).Nonempty) :
          ∃ (b : Fin 2) (c : Fin n) (X : Finset (Fin n)),
          c ∈ exclusive (n := n) C j (1-b) ∩ exclusive (n := n) C k (1-(r+b)) ∧
          X ⊆ exclusive (n := n) C j b ∩ exclusive (n := n) C k (r+b) ∧
          X.Nonempty ∧ (E r) ⊆ X.image (fun x => s(c,x)) ∧ ∀ x ∈ X, s(c,x) ∈ Ustar G C := by
        rcases blockStarExtract h4 (E := E r) Finset.inter_subset_right hn (adj r) with
          ⟨c,hc,X,hX,hne,hcov,h⟩ | ⟨c,hc,X,hX,hne,hcov,h⟩
        · refine ⟨0,c,X,?_,?_,hne,hcov,fun x hx => (Finset.mem_sdiff.mp (Finset.mem_inter.mp (h x hx)).1).1⟩
          · simpa [B] using hc
          · simpa [A] using hX
        · refine ⟨1,c,X,?_,?_,hne,hcov,fun x hx => (Finset.mem_sdiff.mp (Finset.mem_inter.mp (h x hx)).1).1⟩
          · fin_cases r <;> simpa [A] using hc
          · simpa [B,oppositeAddOne] using hX
      have cover : R ⊆ E 0 ∪ E 1 := by
        intro e h
        induction e using Sym2.ind with
        | h x y =>
          obtain ⟨joint,hjv,hkv⟩ := residualJoint hL hT hs h
          have hL' := junkOrientation hL.1 hT hs joint h hjv hkv
          have hR' := junkOrientation hL.1 hT sk (joint_comm joint) h hkv hjv
          have put (p q : Fin n) (r : Fin 2) (hp : p ∈ A r) (hq : q ∈ B r)
              (eq : s(p,q) = s(x,y)) : s(x,y) ∈ E r :=
            Finset.mem_inter.mpr ⟨h, Finset.mem_image.mpr
              ⟨(p,q),Finset.mem_product.mpr ⟨hp,hq⟩,eq⟩⟩
          apply Finset.mem_union.mpr
          rcases hL' with ⟨l,r⟩ | ⟨l,r⟩ <;> rcases hR' with ⟨l',r'⟩ | ⟨l',r'⟩
          · exact .inl (put x y 0 (Finset.mem_inter.mpr ⟨l,l'⟩)
              (Finset.mem_inter.mpr ⟨r,r'⟩) rfl)
          · exact .inr (put x y 1 (Finset.mem_inter.mpr ⟨l,r'⟩)
              (Finset.mem_inter.mpr ⟨r,l'⟩) rfl)
          · exact .inr (put y x 1 (Finset.mem_inter.mpr ⟨l,r'⟩)
              (Finset.mem_inter.mpr ⟨r,l'⟩) Sym2.eq_swap)
          · exact .inl (put y x 0 (Finset.mem_inter.mpr ⟨l,l'⟩)
              (Finset.mem_inter.mpr ⟨r,r'⟩) Sym2.eq_swap)
      have single_budget {r : Fin 2} {b : Fin 2} {c : Fin n} {X : Finset (Fin n)}
          (hX : X ⊆ exclusive (n := n) C j b ∩ exclusive (n := n) C k (r+b))
          (hex : ∀ x ∈ X, s(c,x) ∈ Ustar G C) : X.card+1 ≤ (orN G C \ lam G C).card+2 := by
        have hroot := (opndBound hL.1 (junkData hj).1 b).trans (Nat.add_lt_add_left (junkData hj).1 n)
        have hside : X ⊆ side (n := n) C j b := fun x hx =>
          (Finset.mem_sdiff.mp (Finset.mem_inter.mp (hX hx)).1).1
        obtain ⟨P,hP,hcount,_⟩ := starLeafBudget hL.1 h4 hroot hside hex
        have hp := Finset.card_le_card hP
        omega
      by_cases h0 : (E 0).Nonempty
      · obtain ⟨b,c,X,hc,hX,hXne,hcovX,hex⟩ := star 0 h0
        by_cases h1 : (E 1).Nonempty
        · obtain ⟨d,f,Y,hf,hY,hYne,hcovY,hey⟩ := star 1 h1
          have hx' : X ⊆ exclusive (n := n) C j b ∩ exclusive (n := n) C k b := by simpa using hX
          have hc' : c ∈ exclusive (n := n) C j (1-b) ∩ exclusive (n := n) C k (1-b) := by simpa using hc
          have hf' : f ∈ exclusive (n := n) C j (1-d) ∩ exclusive (n := n) C k d := by
            fin_cases d <;> simpa using hf
          have hcost := crossed_stars_budget hL.1 h4 s hbip (junkData hj).1 (junkData hk).1 hx' hY hc' hf' hex hey
          apply two_star_package hXne hYne
          · exact cover.trans (Finset.union_subset_union hcovX hcovY)
          · exact fun x hx => SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (hex x hx)).1
          · exact fun y hy => SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (hey y hy)).1
          · omega
        · have he1 := Finset.not_nonempty_iff_eq_empty.mp h1
          have cov : R ⊆ X.image (fun x => s(c,x)) := by
            have he : R ⊆ E 0 := by simpa [he1] using cover
            exact he.trans hcovX
          exact one_star_package hXne cov
            (fun x hx => SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (hex x hx)).1)
            (single_budget hX hex)
      · have he0 := Finset.not_nonempty_iff_eq_empty.mp h0
        have he1 : (E 1).Nonempty := by
          have hsub : R ⊆ E 1 := by simpa [he0] using cover
          exact ⟨s(u,v),hsub he⟩
        obtain ⟨d,f,Y,hf,hY,hYne,hcovY,hey⟩ := star 1 he1
        have cov : R ⊆ Y.image (fun y => s(f,y)) := by
          have he : R ⊆ E 1 := by simpa [he0] using cover
          exact he.trans hcovY
        exact one_star_package hYne cov
          (fun y hy => SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (hey y hy)).1)
          (single_budget hY hey)
  · refine ⟨∅,fun _ => ∅,by simp,by simp,?_,by simp⟩
    intro e he
    exact (hR ⟨e,he⟩).elim

lemma empty_wmax_centerless (hL : IsLeastAO G C) (hT : TopForm G C)
    (hw : ∀ j ∈ junk G C, wmax G C j = ∅) (hU : (Ustar G C).Nonempty) :
    (centreless G C).Nonempty := by
  obtain ⟨e,he⟩ := hU
  induction e using Sym2.ind with
  | h u v =>
    have hadj : G.Adj u v := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp he).1
    obtain ⟨a,ha,hv⟩ := acceptedTop hL hadj
    obtain ⟨hl,ho,hb⟩ := topData ha
    have traces (b : Fin 2) := operandSupport hL.1 hT hl ho
      ((andValOperands hL.1 hl ho (pairInput u v)).mp hv b)
    have empty_side {g : ℕ} {b : Fin 2} (hg : g ∈ junk G C)
        (hr : OrReaches n C (opnd C a b) g) : side (n := n) C a (1-b) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hm := oppositeSideWmax hL.1 ha hr hx
      rw [hw g hg] at hm
      exact Finset.notMem_empty x hm
    rcases traces 0 with ⟨x,hx,hxe⟩ | ⟨g,hg,hrg,hvg⟩
    · rcases traces 1 with ⟨y,hy,hye⟩ | ⟨g,hg,hrg,hvg⟩
      · have hxy := G.ne_of_adj (topAdj hL.1 ha hx hy)
        have eq : s(u,v) = s(x,y) := by
          rcases hxe with rfl | rfl <;> rcases hye with rfl | rfl
          · exact (hxy rfl).elim
          · rfl
          · exact Sym2.eq_swap
          · exact (hxy rfl).elim
        exact ((Finset.mem_sdiff.mp he).2 (eq ▸ Finset.mem_biUnion.mpr ⟨a,ha,
          Finset.mem_image.mpr ⟨(x,y),Finset.mem_product.mpr ⟨hx,hy⟩,rfl⟩⟩)).elim
      · refine ⟨a,Finset.mem_filter.mpr ⟨ha,Or.inl ?_⟩⟩
        simpa using empty_side hg hrg
    · refine ⟨a,Finset.mem_filter.mpr ⟨ha,Or.inr ?_⟩⟩
      simpa using empty_side hg hrg

lemma empty_wmax_star_cover (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v) (h4 : NoFourCycle G)
    (hL : IsLeastAO G C) (hT : TopForm G C) (hTwo : (junk G C).card = 2)
    (hw : ∀ j ∈ junk G C, wmax G C j = ∅) :
    ∃ (Z : Finset (Fin n)) (L : Fin n → Finset (Fin n)),
      (∀ v ∈ Z, (L v).Nonempty) ∧ (∀ v ∈ Z, ∀ u ∈ L v, G.Adj v u) ∧
      (∀ e ∈ Ustar G C, ∃ v ∈ Z, ∃ u ∈ L v, e = s(v,u)) ∧
      (∑ v ∈ Z, (L v).card) + Z.card ≤ (orN G C \ lam G C).card + 2 := by
  have h := residual_star_cover s hbip h4 hL hT hTwo
  rw [coveredByJunk_empty hw, Finset.sdiff_empty] at h
  exact h

end MutualBudget

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.Core

lemma no_two_junk_with_empty_wmax {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G) (hL : IsLeastAO G C) (hT : TopForm G C)
    (hLift : IsLiftFixedPoint G C) (hTwo : (junk G C).card = 2)
    (hne : ∃ u v : Fin n, G.Adj u v) (hw : ∀ j ∈ junk G C, wmax G C j = ∅) : False := by
  obtain ⟨g, h, hgh, hj⟩ := Finset.card_eq_two.mp hTwo
  have hmem : ∀ k, k ∈ junk G C ↔ k = g ∨ k = h := by
    intro k
    rw [hj]
    simp
  have bound (Z : Finset (Fin n)) (L : Fin n → Finset (Fin n))
      (hln : ∀ v ∈ Z, (L v).Nonempty)
      (hla : ∀ v ∈ Z, ∀ u ∈ L v, G.Adj v u)
      (hc : ∀ e ∈ Ustar G C, ∃ v ∈ Z, ∃ u ∈ L v, e = s(v,u)) :
      2 * (centreless G C).card + (orN G C \ lam G C).card + 2 ≤
        (∑ v ∈ Z, (L v).card) + Z.card := by
    simpa only [Finset.sdiff_empty] using
      Surgery.master_surgery_bound hL hLift h4 hgh hmem hne Z ∅ L (fun _ => 0)
        (by simp) hln hla hc (by simp) (by simp) (by simp)
  by_cases hU : (Ustar G C).Nonempty
  · obtain ⟨Z, L, hln, hla, hc, hcost⟩ :=
      MutualBudget.empty_wmax_star_cover s hbip h4 hL hT hTwo hw
    have hbound := bound Z L hln hla hc
    have hpos := Finset.card_pos.mpr (MutualBudget.empty_wmax_centerless hL hT hw hU)
    omega
  · have hbound := bound ∅ (fun _ => ∅) (by simp) (by simp) (by
      intro e he
      exact (hU ⟨e, he⟩).elim)
    simp at hbound


open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.Core

lemma some_junk_has_wmax {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G) (hL : IsLeastAO G C) (hT : TopForm G C)
    (hLift : IsLiftFixedPoint G C) (hTwo : (junk G C).card = 2) :
    ∃ j ∈ junk G C, (wmax G C j).Nonempty := by
  classical
  by_contra hnone
  have hw : ∀ j ∈ junk G C, wmax G C j = ∅ := by
    intro j hj
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro hn
    exact hnone ⟨j, hj, hn⟩
  have hne := edge_exists_of_nonempty_junk hL (Finset.card_pos.mp (by omega))
  exact no_two_junk_with_empty_wmax G C s hbip h4 hL hT hLift hTwo hne hw

lemma normalized_two_junk_with_guard {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G) (hL : IsLeastAO G C) (hTwo : (junk G C).card = 2) :
    ∃ D : Circuit, IsLeastAO G D ∧ D.size = C.size ∧ (junk G D).card = 2 ∧
      TopForm G D ∧ IsLiftFixedPoint G D ∧ ∃ j ∈ junk G D, (wmax G D j).Nonempty := by
  obtain ⟨D, hD, hsize, hDtwo, htop, hfixed, _⟩ := normalized_two_junk G C hL hTwo
  exact ⟨D, hD, hsize, hDtwo, htop, hfixed,
    some_junk_has_wmax G D s hbip h4 hD htop hfixed hDtwo⟩

end PEqualNP.Outside.L_meta_5012
