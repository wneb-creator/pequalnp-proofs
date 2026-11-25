import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2685.LibraryRoute

namespace A1501

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

end A1501
namespace Glue

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

lemma exists_least (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C' : Circuit)
    (h1 : PEqualNP.TopForm.IsAO2 n C') (h2 : circuitFun n C' = graphFun G ∅) :
    ∃ C : Circuit, PEqualNP.TopForm.IsLeastAO G C ∧ C.size ≤ C'.size := by
  classical
  have hex : ∃ k : ℕ, ∃ C : Circuit, PEqualNP.TopForm.IsAO2 n C ∧ circuitFun n C = graphFun G ∅ ∧
      C.size = k := ⟨_, C', h1, h2, rfl⟩
  obtain ⟨C, hC1, hC2, hC3⟩ := Nat.find_spec hex
  refine ⟨C, ⟨hC1, hC2, ?_⟩, ?_⟩
  · intro D hD1 hD2
    rw [hC3]
    exact Nat.find_min' hex ⟨D, hD1, hD2, rfl⟩
  · rw [hC3]
    exact Nat.find_min' hex ⟨C', h1, h2, rfl⟩

end Glue

lemma leastTopFormAO (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : PEqualNP.CircuitLowerBounds.Circuit) (hne : G.edgeFinset.Nonempty)
    (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hF : PEqualNP.MetaComplexity.circuitFun n C =
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅) :
    ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.TopForm.IsLeastAO G D ∧ PEqualNP.TopForm.TopForm G D ∧ D.size ≤ C.size := by
  obtain ⟨C2, hL2, hS2⟩ := Glue.exists_least n G C hAO hF
  obtain ⟨D, hLD, hSD, _, hTD⟩ := A1501.main_ind n G hne _ C2 hL2 rfl
  exact ⟨D, hLD, hTD, by omega⟩

end PEqualNP.Outside.L_meta_2685.LibraryRoute

namespace PEqualNP.Outside.L_meta_2685_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.EdgeOwnership

def back (B : ℕ) (gs : List Gate) : Prop :=
  ∀ i < gs.length, ∀ u ∈ (gs.getD i ⟨GateOp.or, []⟩).inputs, u < B + i

lemma back_append (B : ℕ) (gs hs : List Gate)
    (hg : back B gs) (hh : back (B + gs.length) hs) : back B (gs ++ hs) := by
  intro i hi u hu
  by_cases h : i < gs.length
  · have he : (gs ++ hs).getD i ⟨GateOp.or, []⟩ = gs.getD i ⟨GateOp.or, []⟩ := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
    rw [he] at hu
    exact hg i h u hu
  · have he : (gs ++ hs).getD i ⟨GateOp.or, []⟩ =
        hs.getD (i - gs.length) ⟨GateOp.or, []⟩ := by
      simp only [List.getD_eq_getElem?_getD,
        List.getElem?_append_right (show gs.length ≤ i by omega)]
    rw [he] at hu
    have hix : i - gs.length < hs.length := by simp only [List.length_append] at hi; omega
    have hu' := hh (i - gs.length) hix u hu
    omega

lemma block_length (B a t v : ℕ) (rest : List ℕ) (lead : Bool) :
    (blockGates B a t v rest lead).length = rest.length + 1 + (if lead then 0 else 1) := by
  cases lead <;> simp [blockGates]

lemma chain_wire_lt (B v : ℕ) (rest : List ℕ) (hv : v < B) (i : ℕ)
    (hi : i ≤ rest.length) :
    (v :: (List.range rest.length).map (fun j => B + j)).getD i 0 < B + i := by
  cases i with
  | zero => simpa using hv
  | succ i =>
    have hi' : i < rest.length := by omega
    simp [List.getD_cons_succ, List.getD_eq_getElem?_getD, hi']

lemma block_back (B a t v : ℕ) (rest : List ℕ) (lead : Bool)
    (ha : lead = false → a < B) (ht : t < B) (hv : v < B)
    (hr : ∀ u ∈ rest, u < B) : back B (blockGates B a t v rest lead) := by
  unfold blockGates
  apply back_append
  · intro i hi u hu
    have hi' : i < rest.length := by simpa using hi
    have hp := chain_wire_lt B v rest hv i hi'.le
    have hrest : rest.getD i 0 < B := by
      rw [List.getD_eq_getElem _ _ hi']
      exact hr _ (List.getElem_mem hi')
    have he : ((List.range rest.length).map (fun i =>
        (⟨GateOp.or, [(v :: (List.range rest.length).map (fun j => B + j)).getD i 0,
          rest.getD i 0]⟩ : Gate))).getD i ⟨GateOp.or, []⟩ =
        ⟨GateOp.or, [(v :: (List.range rest.length).map (fun j => B + j)).getD i 0,
          rest.getD i 0]⟩ := by
      simp [List.getD_eq_getElem?_getD, hi']
    rw [he] at hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl <;> omega
  · have hp := chain_wire_lt B v rest hv rest.length le_rfl
    simp only [List.length_map, List.length_range]
    intro i hi u hu
    cases lead with
    | true =>
      have hi0 : i = 0 := by simpa using hi
      subst i
      simp only [ite_true, List.getD_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl <;> omega
    | false =>
      have hab := ha rfl
      have hil : i < 2 := by simpa using hi
      interval_cases i <;>
        simp only [Bool.false_eq_true, ite_false, List.getD_cons_zero, List.getD_cons_succ,
          List.mem_cons, List.not_mem_nil, or_false] at hu
      · rcases hu with rfl | rfl <;> omega
      · rcases hu with rfl | rfl <;> omega

lemma gates_back : ∀ (own : List (ℕ × List ℕ)) (n B : ℕ) (lead : Bool) (a : ℕ),
    n ≤ B → (lead = false → a < B) →
    (∀ tx ∈ own, tx.1 < n ∧ ∀ u ∈ tx.2, u < n) →
    back B (coverGatesB B lead a own)
  | [], _, _, _, _, _, _, _ => by simp [back, coverGatesB]
  | (_, []) :: os, n, B, lead, a, hn, ha, ho => by
      exact gates_back os n B lead a hn ha (fun tx htx => ho tx (List.mem_cons_of_mem _ htx))
  | (t, v :: rest) :: os, n, B, lead, a, hn, ha, ho => by
      have ht := (ho (t, v :: rest) (by simp)).1
      have hv := (ho (t, v :: rest) (by simp)).2 v (by simp)
      have hr (u : ℕ) (hu : u ∈ rest) := (ho (t, v :: rest) (by simp)).2 u (by simp [hu])
      have hlen : 0 < (blockGates B a t v rest lead).length := by rw [block_length]; omega
      apply back_append
      · exact block_back B a t v rest lead ha (by omega) (by omega)
          (fun u hu => by have := hr u hu; omega)
      · exact gates_back os n _ false _ (by omega) (fun _ => by omega)
          (fun tx htx => ho tx (List.mem_cons_of_mem _ htx))

lemma block_shape (B a t v : ℕ) (rest : List ℕ) (lead : Bool) :
    ∀ g ∈ blockGates B a t v rest lead,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
  intro g hg
  cases lead <;> simp [blockGates] at hg <;> rcases hg with ⟨i, _, rfl⟩ | rfl | rfl <;> simp

lemma gates_shape : ∀ (own : List (ℕ × List ℕ)) (B : ℕ) (lead : Bool) (a : ℕ),
    ∀ g ∈ coverGatesB B lead a own,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2
  | [], _, _, _ => by intro g hg; simp [coverGatesB] at hg
  | (_, []) :: os, B, lead, a => by
      intro g hg
      exact gates_shape os B lead a g hg
  | (t, v :: rest) :: os, B, lead, a => by
      intro g hg
      simp only [coverGatesB, List.mem_append] at hg
      rcases hg with hg | hg
      · exact block_shape B a t v rest lead g hg
      · exact gates_shape os _ false _ g hg

lemma coverCircuitB_isAO2 (n : ℕ) (own : List (ℕ × List ℕ))
    (ho : ∀ tx ∈ own, tx.1 < n ∧ ∀ u ∈ tx.2, u < n) :
    IsAO2 n (coverCircuitB n own) := by
  have hg := gates_shape own n true 0
  have hb := gates_back own n n true 0 le_rfl (by simp) ho
  unfold coverCircuitB
  split_ifs
  · simp [IsAO2, AndOrOnly, ReadsBack]
  · exact ⟨fun g h => (hg g h).1, hb, fun g h => (hg g h).2⟩

def closed (B : ℕ) (gs : List Gate) (base S : Finset ℕ) : Prop :=
  ∀ w ∈ S, w ∈ base ∨ ∃ i < gs.length, w = B + i ∧
    (gs.getD i ⟨GateOp.or, []⟩).op = GateOp.or ∧
    ∀ u ∈ (gs.getD i ⟨GateOp.or, []⟩).inputs, u ∈ S

def shaped (B : ℕ) (gs : List Gate) (P0 L0 P L : Finset ℕ) : Prop :=
  closed B gs P0 P ∧ closed B gs L0 L ∧
  ∀ i < gs.length, (gs.getD i ⟨GateOp.or, []⟩).op = GateOp.and →
    ∃ a b, (gs.getD i ⟨GateOp.or, []⟩).inputs = [a,b] ∧
      ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P))

lemma gate_append_left (gs hs : List Gate) (i : ℕ) (hi : i < gs.length) :
    (gs ++ hs).getD i ⟨GateOp.or, []⟩ = gs.getD i ⟨GateOp.or, []⟩ := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma gate_append_right (gs hs : List Gate) (i : ℕ) :
    (gs ++ hs).getD (gs.length + i) ⟨GateOp.or, []⟩ = hs.getD i ⟨GateOp.or, []⟩ := by
  simp only [List.getD_eq_getElem?_getD,
    List.getElem?_append_right (show gs.length ≤ gs.length + i by omega),
    Nat.add_sub_cancel_left]

lemma closed_append (B : ℕ) (gs hs : List Gate) (base S T : Finset ℕ)
    (hS : closed B gs base S) (hT : closed (B + gs.length) hs base T) :
    closed B (gs ++ hs) base (S ∪ T) := by
  intro w hw
  rcases Finset.mem_union.mp hw with hw | hw
  · rcases hS w hw with hw | ⟨i,hi,he,hop,hu⟩
    · exact Or.inl hw
    · refine Or.inr ⟨i,by simp; omega,he,?_,?_⟩
      · simpa only [gate_append_left gs hs i hi] using hop
      · intro u hum
        have hu' : u ∈ S := hu u (by simpa only [gate_append_left gs hs i hi] using hum)
        exact Finset.mem_union_left T hu'
  · rcases hT w hw with hw | ⟨i,hi,he,hop,hu⟩
    · exact Or.inl hw
    · refine Or.inr ⟨gs.length+i,by simp; omega,by omega,?_,?_⟩
      · simpa only [gate_append_right] using hop
      · intro u hum
        have hu' : u ∈ T := hu u (by simpa only [gate_append_right] using hum)
        exact Finset.mem_union_right S hu'

lemma shaped_append (B : ℕ) (gs hs : List Gate) (P0 L0 P L P' L' : Finset ℕ)
    (hg : shaped B gs P0 L0 P L) (hh : shaped (B + gs.length) hs P0 L0 P' L') :
    shaped B (gs ++ hs) P0 L0 (P ∪ P') (L ∪ L') := by
  refine ⟨closed_append B gs hs P0 P P' hg.1 hh.1,
    closed_append B gs hs L0 L L' hg.2.1 hh.2.1,?_⟩
  intro i hi hop
  by_cases hx : i < gs.length
  · obtain ⟨a,b,he,ha⟩ := hg.2.2 i hx (by simpa only [gate_append_left gs hs i hx] using hop)
    refine ⟨a,b,by simpa only [gate_append_left gs hs i hx] using he,?_⟩
    rcases ha with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · exact Or.inl ⟨Finset.mem_union_left _ ha,Finset.mem_union_left _ hb⟩
    · exact Or.inr ⟨Finset.mem_union_left _ ha,Finset.mem_union_left _ hb⟩
  · have hie : i = gs.length + (i-gs.length) := by omega
    have hix : i-gs.length < hs.length := by simp only [List.length_append] at hi; omega
    rw [hie,gate_append_right] at hop
    obtain ⟨a,b,he,ha⟩ := hh.2.2 (i-gs.length) hix hop
    refine ⟨a,b,?_,?_⟩
    · rw [hie,gate_append_right]
      exact he
    rcases ha with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · exact Or.inl ⟨Finset.mem_union_right _ ha,Finset.mem_union_right _ hb⟩
    · exact Or.inr ⟨Finset.mem_union_right _ ha,Finset.mem_union_right _ hb⟩

lemma shaped_swap (B : ℕ) (gs : List Gate) (P0 L0 P L : Finset ℕ)
    (h : shaped B gs P0 L0 P L) : shaped B gs L0 P0 L P := by
  refine ⟨h.2.1,h.1,?_⟩
  intro i hi hop
  obtain ⟨a,b,he,ha⟩ := h.2.2 i hi hop
  exact ⟨a,b,he,ha.symm⟩

def chainWires (B : ℕ) (rest : List ℕ) : Finset ℕ :=
  (Finset.range rest.length).image (fun i => B+i)

lemma chain_wire_mem (B v : ℕ) (rest : List ℕ) (L0 : Finset ℕ) (hv : v ∈ L0)
    (i : ℕ) (hi : i ≤ rest.length) :
    (v :: (List.range rest.length).map (fun j => B+j)).getD i 0 ∈ L0 ∪ chainWires B rest := by
  cases i with
  | zero => exact Finset.mem_union_left _ hv
  | succ i =>
    have hi' : i < rest.length := by omega
    have he : (v :: (List.range rest.length).map (fun j => B+j)).getD (i+1) 0 = B+i := by
      simp [List.getD_eq_getElem?_getD,hi']
    rw [he]
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_range.mpr hi',rfl⟩)

lemma block_chain (B a t v : ℕ) (rest : List ℕ) (lead : Bool) (i : ℕ) (hi : i < rest.length) :
    (blockGates B a t v rest lead).getD i ⟨GateOp.or,[]⟩ =
      ⟨GateOp.or,[(v :: (List.range rest.length).map (fun j => B+j)).getD i 0,rest.getD i 0]⟩ := by
  unfold blockGates
  rw [gate_append_left _ _ i (by simpa using hi)]
  simp [List.getD_eq_getElem?_getD,hi]

lemma block_and (B a t v : ℕ) (rest : List ℕ) (lead : Bool) :
    (blockGates B a t v rest lead).getD rest.length ⟨GateOp.or,[]⟩ =
      ⟨GateOp.and,[t,(v :: (List.range rest.length).map (fun j => B+j)).getD rest.length 0]⟩ := by
  unfold blockGates
  rw [List.getD_eq_getElem?_getD,List.getElem?_append_right (by simp)]
  simp

lemma block_is_and (B a t v : ℕ) (rest : List ℕ) (lead : Bool) (i : ℕ)
    (hi : i < (blockGates B a t v rest lead).length)
    (hop : ((blockGates B a t v rest lead).getD i ⟨GateOp.or,[]⟩).op = GateOp.and) :
    i = rest.length := by
  by_cases h : i < rest.length
  · rw [block_chain B a t v rest lead i h] at hop
    contradiction
  · rw [block_length] at hi
    have hc : i = rest.length ∨ i = rest.length+1 := by split_ifs at hi <;> omega
    rcases hc with he | he
    · exact he
    · have hl : lead = false := by cases lead <;> simp_all
      subst lead
      subst i
      unfold blockGates at hop
      rw [List.getD_eq_getElem?_getD,List.getElem?_append_right (by simp)] at hop
      simp at hop

lemma block_shaped (B a t v : ℕ) (rest : List ℕ) (lead : Bool) (P0 L0 : Finset ℕ)
    (ht : t ∈ P0) (hv : v ∈ L0) (hr : ∀ u ∈ rest, u ∈ L0) :
    shaped B (blockGates B a t v rest lead) P0 L0 P0 (L0 ∪ chainWires B rest) := by
  refine ⟨fun w hw => Or.inl hw,?_,?_⟩
  · intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact Or.inl hw
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hw
      have hi' : i < rest.length := Finset.mem_range.mp hi
      refine Or.inr ⟨i,?_,rfl,?_,?_⟩
      · rw [block_length]; omega
      · simp only [block_chain B a t v rest lead i hi']
      · rw [block_chain B a t v rest lead i hi']
        intro u hu
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hu
        rcases hu with rfl | rfl
        · exact chain_wire_mem B v rest L0 hv i hi'.le
        · apply Finset.mem_union_left
          rw [List.getD_eq_getElem _ _ hi']
          exact hr _ (List.getElem_mem hi')
  · intro i hi hop
    have he := block_is_and B a t v rest lead i hi hop
    subst i
    rw [block_and]
    exact ⟨t,_,rfl,Or.inl ⟨ht,chain_wire_mem B v rest L0 hv rest.length le_rfl⟩⟩

lemma gates_shaped : ∀ (own : List (ℕ × List ℕ)) (B : ℕ) (lead : Bool) (a : ℕ)
    (P0 L0 : Finset ℕ),
    (∀ tx ∈ own, (tx.1 ∈ P0 ∧ ∀ u ∈ tx.2, u ∈ L0) ∨
      (tx.1 ∈ L0 ∧ ∀ u ∈ tx.2, u ∈ P0)) →
    ∃ P L : Finset ℕ, shaped B (coverGatesB B lead a own) P0 L0 P L
  | [], B, lead, a, P0, L0, _ => by
      refine ⟨P0,L0,fun w hw => Or.inl hw,fun w hw => Or.inl hw,?_⟩
      simp [coverGatesB]
  | (_, []) :: os, B, lead, a, P0, L0, ho => by
      exact gates_shaped os B lead a P0 L0 (fun tx htx => ho tx (List.mem_cons_of_mem _ htx))
  | (t, v :: rest) :: os, B, lead, a, P0, L0, ho => by
      obtain ⟨P,L,hPL⟩ := gates_shaped os
        (B + (blockGates B a t v rest lead).length) false
        (B + (blockGates B a t v rest lead).length - 1) P0 L0
        (fun tx htx => ho tx (List.mem_cons_of_mem _ htx))
      rcases ho (t,v :: rest) (by simp) with ⟨ht,hr⟩ | ⟨ht,hr⟩
      · have hblock := block_shaped B a t v rest lead P0 L0 ht
          (hr v (by simp)) (fun u hu => hr u (by simp [hu]))
        exact ⟨_,_,shaped_append B _ _ P0 L0 _ _ P L hblock hPL⟩
      · have hblock := shaped_swap B _ L0 P0 _ _
          (block_shaped B a t v rest lead L0 P0 ht
            (hr v (by simp)) (fun u hu => hr u (by simp [hu])))
        exact ⟨_,_,shaped_append B _ _ P0 L0 _ _ P L hblock hPL⟩

lemma coverCircuitB_gates (n : ℕ) (own : List (ℕ × List ℕ)) :
    (coverCircuitB n own).gates = coverGatesB n true 0 own := by
  unfold coverCircuitB
  split_ifs with h
  · exact h.symm
  · rfl

lemma coverCircuitB_twoLevel (Np Nl : ℕ) (own : List (ℕ × List ℕ))
    (ho : ∀ tx ∈ own,
      (tx.1 < Np ∧ ∀ u ∈ tx.2, Np ≤ u ∧ u < Np+Nl) ∨
      (Np ≤ tx.1 ∧ tx.1 < Np+Nl ∧ ∀ u ∈ tx.2, u < Np)) :
    ∃ P L : Finset ℕ, IsAO2 (Np+Nl) (coverCircuitB (Np+Nl) own) ∧
      (∀ w ∈ P, w < Np ∨ ∃ i < (coverCircuitB (Np+Nl) own).gates.length,
        w = Np+Nl+i ∧ (gateAt (coverCircuitB (Np+Nl) own) i).op = GateOp.or ∧
        ∀ u ∈ (gateAt (coverCircuitB (Np+Nl) own) i).inputs, u ∈ P) ∧
      (∀ w ∈ L, (Np ≤ w ∧ w < Np+Nl) ∨
        ∃ i < (coverCircuitB (Np+Nl) own).gates.length,
        w = Np+Nl+i ∧ (gateAt (coverCircuitB (Np+Nl) own) i).op = GateOp.or ∧
        ∀ u ∈ (gateAt (coverCircuitB (Np+Nl) own) i).inputs, u ∈ L) ∧
      ∀ i < (coverCircuitB (Np+Nl) own).gates.length,
        (gateAt (coverCircuitB (Np+Nl) own) i).op = GateOp.and →
        ∃ a b : ℕ, (gateAt (coverCircuitB (Np+Nl) own) i).inputs = [a,b] ∧
          ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P)) := by
  have htag : ∀ tx ∈ own,
      (tx.1 ∈ Finset.range Np ∧ ∀ u ∈ tx.2, u ∈ Finset.Ico Np (Np+Nl)) ∨
      (tx.1 ∈ Finset.Ico Np (Np+Nl) ∧ ∀ u ∈ tx.2, u ∈ Finset.range Np) := by
    simpa only [Finset.mem_range,Finset.mem_Ico,and_assoc] using ho
  obtain ⟨P,L,hshape⟩ := gates_shaped own (Np+Nl) true 0 (Finset.range Np)
    (Finset.Ico Np (Np+Nl)) htag
  have hb : ∀ tx ∈ own, tx.1 < Np+Nl ∧ ∀ u ∈ tx.2, u < Np+Nl := by
    intro tx htx
    rcases ho tx htx with ⟨ht,hu⟩ | ⟨ht,ht',hu⟩
    · exact ⟨by omega,fun u h => (hu u h).2⟩
    · exact ⟨ht',fun u h => by have := hu u h; omega⟩
  refine ⟨P,L,coverCircuitB_isAO2 (Np+Nl) own hb,?_,?_,?_⟩
  · simpa only [closed,Finset.mem_range,gateAt,coverCircuitB_gates] using hshape.1
  · simpa only [closed,Finset.mem_Ico,gateAt,coverCircuitB_gates] using hshape.2.1
  · simpa only [gateAt,coverCircuitB_gates] using hshape.2.2




lemma gates_length_false : ∀ (own : List (ℕ × List ℕ)) (B a : ℕ), (∀ p ∈ own, p.2 ≠ []) →
    (coverGatesB B false a own).length =
      (own.map (fun p : ℕ × List ℕ => p.2.length)).sum + own.length
  | [], _, _, _ => by simp [coverGatesB]
  | (t, []) :: os, B, a, h => by simp at h
  | (t, v1 :: rest) :: os, B, a, h => by
      have ih := gates_length_false os (B + (blockGates B a t v1 rest false).length)
        (B + (blockGates B a t v1 rest false).length - 1)
        (fun p hp => h p (List.mem_cons_of_mem _ hp))
      simp only [coverGatesB, List.length_append]
      rw [ih, block_length]
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      simp
      omega

lemma circuit_size (n : ℕ) (own : List (ℕ × List ℕ)) (hne : own ≠ [])
    (h : ∀ p ∈ own, p.2 ≠ []) :
    (coverCircuitB n own).size + 1 =
      (own.map (fun p : ℕ × List ℕ => p.2.length)).sum + own.length := by
  match own, hne, h with
  | (t, []) :: os, _, h => simp at h
  | (t, v1 :: rest) :: os, _, h =>
      have ih := gates_length_false os (n + (blockGates n 0 t v1 rest true).length)
        (n + (blockGates n 0 t v1 rest true).length - 1)
        (fun p hp => h p (List.mem_cons_of_mem _ hp))
      have hgl : (coverGatesB n true 0 ((t, v1 :: rest) :: os)).length =
          rest.length + 1 + ((os.map (fun p : ℕ × List ℕ => p.2.length)).sum + os.length) := by
        simp only [coverGatesB, List.length_append]
        rw [ih, block_length]
        simp
      have hnn : coverGatesB n true 0 ((t, v1 :: rest) :: os) ≠ [] := by
        intro h0
        have h1 := congrArg List.length h0
        rw [hgl] at h1
        simp at h1
      unfold coverCircuitB Circuit.size
      rw [if_neg hnn]
      simp only [hgl, List.map_cons, List.sum_cons, List.length_cons]
      omega




def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

lemma fold_app (gs : List Gate) : ∀ w : List Bool, ∃ t : List Bool,
    gs.foldl step w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (step w g)
    refine ⟨(g.op.eval (g.inputs.map fun i => w.getD i false)) :: t, ?_, ?_⟩
    · rw [List.foldl_cons, ht]; simp [step]
    · simp [hl]

lemma getD_app_left {w t : List Bool} {i : ℕ} (h : i < w.length) :
    (w ++ t).getD i false = w.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h, ← List.getD_eq_getElem?_getD]

lemma getD_app_right {w t : List Bool} {i : ℕ} :
    (w ++ t).getD (w.length + i) false = t.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    ← List.getD_eq_getElem?_getD]

lemma getD_snoc' (l : List Bool) (b : Bool) (i : ℕ) (h : i = l.length) :
    (l ++ [b]).getD i false = b := by
  subst h
  simpa using getD_app_right (w := l) (t := [b]) (i := 0)

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := fold_app gs w
  rw [ht, List.length_append, hl]

lemma fold_keep (gs : List Gate) (w : List Bool) {i : ℕ} (h : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := fold_app gs w
  rw [ht, getD_app_left h]

lemma any_congr_mem {l : List ℕ} {f g : ℕ → Bool} (h : ∀ u ∈ l, f u = g u) :
    l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    simp only [List.any_cons]
    rw [h b (by simp), ih (fun u hu => h u (by simp [hu]))]


def cv (w : List Bool) (v1 : ℕ) (rest : List ℕ) (k : ℕ) : Bool :=
  w.getD v1 false || (rest.take k).any (fun u => w.getD u false)

lemma chain_read (w : List Bool) (B v1 : ℕ) (rest : List ℕ) (hw : w.length = B)
    (hv1 : v1 < B) (k : ℕ) (hk : k ≤ rest.length) :
    (w ++ (List.range k).map (fun i => cv w v1 rest (i + 1))).getD
        ((v1 :: (List.range rest.length).map (fun j => B + j)).getD k 0) false
      = cv w v1 rest k := by
  cases k with
  | zero =>
    simp only [List.getD_cons_zero]
    rw [getD_app_left (by omega)]
    simp [cv]
  | succ j =>
    have hj : j < rest.length := by omega
    have e1 : (v1 :: (List.range rest.length).map (fun j => B + j)).getD (j + 1) 0 = B + j := by
      simp [List.getD_cons_succ, List.getD_eq_getElem?_getD, hj]
    rw [e1, ← hw, getD_app_right]
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (show j < j + 1 by omega)]

lemma chain (w : List Bool) (B v1 : ℕ) (rest : List ℕ) (hw : w.length = B)
    (hv1 : v1 < B) (hrest : ∀ u ∈ rest, u < B) :
    ∀ k ≤ rest.length,
      ((List.range k).map (fun i => (⟨GateOp.or,
          [(v1 :: (List.range rest.length).map (fun j => B + j)).getD i 0, rest.getD i 0]⟩ : Gate))).foldl
        step w = w ++ (List.range k).map (fun i => cv w v1 rest (i + 1)) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    rw [List.range_succ, List.map_append, List.foldl_append, ih (by omega)]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, step]
    rw [List.append_assoc]
    congr 2
    have hkr : k < rest.length := by omega
    have hrk : rest.getD k 0 = rest[k] := by
      simp [List.getD_eq_getElem?_getD, hkr]
    have hlt : rest[k] < w.length := by rw [hw]; exact hrest _ (List.getElem_mem hkr)
    simp only [List.map_cons, List.map_nil, GateOp.eval]
    rw [chain_read w B v1 rest hw hv1 k (by omega), hrk, getD_app_left hlt]
    simp only [cv, List.take_succ, List.getElem?_eq_getElem hkr, Option.toList_some,
      List.any_append, List.any_cons, List.any_nil, List.any_cons, Bool.or_false, id]
    simp [Bool.or_assoc, List.getElem?_eq_getElem hkr]

lemma block_val (w : List Bool) (B a t v1 : ℕ) (rest : List ℕ) (lead : Bool)
    (hw : w.length = B) (ha : lead = false → a < B) (ht : t < B) (hv1 : v1 < B)
    (hrest : ∀ u ∈ rest, u < B) :
    ((blockGates B a t v1 rest lead).foldl step w).getD
        (B + (blockGates B a t v1 rest lead).length - 1) false
      = if lead then (w.getD t false && (w.getD v1 false || rest.any (fun u => w.getD u false)))
        else (w.getD a false ||
          (w.getD t false && (w.getD v1 false || rest.any (fun u => w.getD u false)))) := by
  have hc := chain w B v1 rest hw hv1 hrest rest.length le_rfl
  have hr := chain_read w B v1 rest hw hv1 rest.length le_rfl
  have hcvr : cv w v1 rest rest.length = (w.getD v1 false || rest.any (fun u => w.getD u false)) := by
    simp [cv]
  set L := (List.range rest.length).map (fun i => cv w v1 rest (i + 1)) with hL
  have hLl : L.length = rest.length := by simp [hL]
  have htW : (w ++ L).getD t false = w.getD t false := getD_app_left (by omega)
  rw [block_length]
  cases lead with
  | true =>
    simp only [blockGates, ↓reduceIte, List.foldl_append, hc, List.foldl_cons, List.foldl_nil,
      step]
    rw [getD_snoc']
    · simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil]
      rw [htW, hr, hcvr]
      simp
    · simp [hLl, hw]
  | false =>
    have ha' : a < B := ha rfl
    simp only [blockGates, Bool.false_eq_true, ↓reduceIte, List.foldl_append, hc, List.foldl_cons,
      List.foldl_nil, step]
    rw [getD_snoc']
    · simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil]
      rw [getD_app_left (by simp; omega), getD_app_left (by omega), getD_snoc']
      · simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil]
        rw [htW, hr, hcvr]
        simp
      · simp [hLl, hw]
    · simp [hLl, hw]


def F (x : List Bool) (own : List (ℕ × List ℕ)) : Bool :=
  own.any (fun p => x.getD p.1 false && p.2.any (fun u => x.getD u false))

lemma gates_nil_F (x : List Bool) : ∀ (own : List (ℕ × List ℕ)) (B : ℕ) (lead : Bool) (a : ℕ),
    coverGatesB B lead a own = [] → F x own = false
  | [], _, _, _, _ => rfl
  | (t, []) :: os, B, lead, a, h => by
      simp only [coverGatesB] at h
      have := gates_nil_F x os B lead a h
      simp only [F, List.any_cons, List.any_nil, Bool.and_false, Bool.false_or] at this ⊢
      exact this
  | (t, v1 :: rest) :: os, B, lead, a, h => by
      simp only [coverGatesB] at h
      cases lead <;> simp [blockGates] at h

lemma main (n : ℕ) (x : List Bool) :
    ∀ (own : List (ℕ × List ℕ)) (B : ℕ) (lead : Bool) (a : ℕ) (w : List Bool),
      (∀ p ∈ own, p.1 < n ∧ ∀ u ∈ p.2, u < n) → w.length = B → n ≤ B →
      (∀ i < n, w.getD i false = x.getD i false) → (lead = false → a < B) →
      coverGatesB B lead a own ≠ [] →
      ((coverGatesB B lead a own).foldl step w).getD
          (B + (coverGatesB B lead a own).length - 1) false
        = if lead then F x own else (w.getD a false || F x own)
  | [], _, _, _, _, _, _, _, _, _, hne => by simp [coverGatesB] at hne
  | (t, []) :: os, B, lead, a, w, hown, hw, hnB, hwx, ha, hne => by
      simp only [coverGatesB] at hne ⊢
      rw [main n x os B lead a w (fun p hp => hown p (List.mem_cons_of_mem _ hp)) hw hnB hwx ha
        hne]
      simp [F]
  | (t, v1 :: rest) :: os, B, lead, a, w, hown, hw, hnB, hwx, ha, _ => by
      have hp := hown (t, v1 :: rest) (by simp)
      have ht : t < n := hp.1
      have hv1 : v1 < n := hp.2 v1 (by simp)
      have hrest : ∀ u ∈ rest, u < n := fun u hu => hp.2 u (by simp [hu])
      have hos : ∀ p ∈ os, p.1 < n ∧ ∀ u ∈ p.2, u < n :=
        fun p hp => hown p (List.mem_cons_of_mem _ hp)
      have hbv := block_val w B a t v1 rest lead hw ha (by omega) (by omega)
        (fun u hu => by have := hrest u hu; omega)
      have hrx : rest.any (fun u => w.getD u false) = rest.any (fun u => x.getD u false) :=
        any_congr_mem (fun u hu => hwx u (hrest u hu))
      rw [hrx, hwx t ht, hwx v1 hv1] at hbv
      set bg := blockGates B a t v1 rest lead with hbg
      have hm : 0 < bg.length := by rw [hbg, block_length]; omega
      set W1 := bg.foldl step w with hW1
      have hW1l : W1.length = B + bg.length := by rw [hW1, fold_length, hw]
      have hW1x : ∀ i < n, W1.getD i false = x.getD i false := by
        intro i hi
        rw [hW1, fold_keep bg w (by omega)]
        exact hwx i hi
      have hW1a : lead = false → W1.getD a false = w.getD a false := by
        intro hl
        rw [hW1, fold_keep bg w (by have := ha hl; omega)]
      have hcons : F x ((t, v1 :: rest) :: os) =
          ((x.getD t false && (x.getD v1 false || rest.any (fun u => x.getD u false))) || F x os) :=
        rfl
      rw [hcons]
      simp only [coverGatesB]
      rw [← hbg, List.foldl_append, ← hW1, List.length_append]
      by_cases hnil : coverGatesB (B + bg.length) false (B + bg.length - 1) os = []
      · have hF := gates_nil_F x os _ false _ hnil
        rw [hnil, List.foldl_nil, List.length_nil, Nat.add_zero, hbv]
        rw [hF]
        cases lead <;> simp
      · have ih := main n x os (B + bg.length) false (B + bg.length - 1) W1 hos hW1l (by omega)
          hW1x (fun _ => by omega) hnil
        have hidx : B + (bg.length + (coverGatesB (B + bg.length) false (B + bg.length - 1) os).length) - 1
            = B + bg.length + (coverGatesB (B + bg.length) false (B + bg.length - 1) os).length - 1 := by
          omega
        rw [hidx, ih, hbv]
        cases lead <;> simp [Bool.or_assoc]

lemma circuit_fun (n : ℕ) (own : List (ℕ × List ℕ))
    (h : ∀ p ∈ own, p.1 < n ∧ ∀ w ∈ p.2, w < n) (x : Fin n → Bool) :
    ((coverCircuitB n own).eval (List.ofFn x) = true ↔
      ∃ p ∈ own, (List.ofFn x).getD p.1 false = true ∧
        ∃ w ∈ p.2, (List.ofFn x).getD w false = true) := by
  have hF : (∃ p ∈ own, (List.ofFn x).getD p.1 false = true ∧
        ∃ w ∈ p.2, (List.ofFn x).getD w false = true) ↔ F (List.ofFn x) own = true := by
    simp [F, List.any_eq_true]
  rw [hF]
  unfold coverCircuitB Circuit.eval
  split_ifs with hnil
  · rw [gates_nil_F _ own n true 0 hnil, wires_eq]
    simp [List.getD_eq_getElem?_getD]
  · rw [wires_eq]
    simp only
    rw [main n (List.ofFn x) own n true 0 (List.ofFn x) h (by simp) le_rfl (fun _ _ => rfl)
      (by simp) hnil]
    simp


lemma coverCircuitB_size_eq (n : ℕ) (own : List (ℕ × List ℕ))
    (ho : ∀ tx ∈ own, tx.2 ≠ []) :
    (coverCircuitB n own).size = (own.map (fun tx => tx.2.length)).sum + own.length - 1 := by
  by_cases hn : own = []
  · subst own
    simp [coverCircuitB,coverGatesB,Circuit.size]
  · have hs := circuit_size n own hn ho
    omega

lemma read_fin (n : ℕ) (z : Fin n → Bool) (i : Fin n) :
    (List.ofFn z).getD i.val false = z i := by
  simp [List.getD_eq_getElem?_getD]

lemma coverCircuitB_incidence (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop)
    [DecidableRel I] (own : List (ℕ × List ℕ))
    (ho : ∀ tx ∈ own,
      (tx.1 < Np ∧ ∀ u ∈ tx.2, Np ≤ u ∧ u < Np+Nl) ∨
      (Np ≤ tx.1 ∧ tx.1 < Np+Nl ∧ ∀ u ∈ tx.2, u < Np))
    (hc : ∀ p l, I p l ↔ ∃ tx ∈ own,
      (tx.1 = p.val ∧ Np+l.val ∈ tx.2) ∨
      (tx.1 = Np+l.val ∧ p.val ∈ tx.2)) :
    ∀ z : Fin (Np+Nl) → Bool, circuitFun (Np+Nl) (coverCircuitB (Np+Nl) own) z =
      decide (∃ p l, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true) := by
  have hb : ∀ tx ∈ own, tx.1 < Np+Nl ∧ ∀ u ∈ tx.2, u < Np+Nl := by
    intro tx htx
    rcases ho tx htx with ⟨ht,hu⟩ | ⟨ht,ht',hu⟩
    · exact ⟨by omega,fun u h => (hu u h).2⟩
    · exact ⟨ht',fun u h => by have := hu u h; omega⟩
  intro z
  apply Bool.eq_iff_iff.mpr
  change ((coverCircuitB (Np+Nl) own).eval (List.ofFn z) = true) ↔ _
  rw [circuit_fun (Np+Nl) own hb z]
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨tx,htx,ht,u,hu,huv⟩
    rcases ho tx htx with ⟨hleft,hr⟩ | ⟨hlo,hhi,hr⟩
    · obtain ⟨hul,huh⟩ := hr u hu
      let p : Fin Np := ⟨tx.1,hleft⟩
      let l : Fin Nl := ⟨u-Np,by omega⟩
      have he : Np+l.val = u := by dsimp [l]; omega
      have hI : I p l := (hc p l).mpr ⟨tx,htx,Or.inl ⟨rfl,he.symm ▸ hu⟩⟩
      have hp : (List.ofFn z).getD tx.1 false = z (Fin.castAdd Nl p) :=
        read_fin (Np+Nl) z (Fin.castAdd Nl p)
      have hl : (List.ofFn z).getD u false = z (Fin.natAdd Np l) := by
        have hh := read_fin (Np+Nl) z (Fin.natAdd Np l)
        simpa only [Fin.val_natAdd,he] using hh
      exact ⟨p,l,hI,hp.symm.trans ht,hl.symm.trans huv⟩
    · have hup := hr u hu
      let p : Fin Np := ⟨u,hup⟩
      let l : Fin Nl := ⟨tx.1-Np,by omega⟩
      have he : Np+l.val = tx.1 := by dsimp [l]; omega
      have hI : I p l := (hc p l).mpr ⟨tx,htx,Or.inr ⟨he.symm,hu⟩⟩
      have hp : (List.ofFn z).getD u false = z (Fin.castAdd Nl p) :=
        read_fin (Np+Nl) z (Fin.castAdd Nl p)
      have hl : (List.ofFn z).getD tx.1 false = z (Fin.natAdd Np l) := by
        have hh := read_fin (Np+Nl) z (Fin.natAdd Np l)
        simpa only [Fin.val_natAdd,he] using hh
      exact ⟨p,l,hI,hp.symm.trans huv,hl.symm.trans ht⟩
  · rintro ⟨p,l,hI,hp,hl⟩
    obtain ⟨tx,htx,h⟩ := (hc p l).mp hI
    have hpv : (List.ofFn z).getD p.val false = true :=
      (read_fin (Np+Nl) z (Fin.castAdd Nl p)).trans hp
    have hlv : (List.ofFn z).getD (Np+l.val) false = true :=
      (read_fin (Np+Nl) z (Fin.natAdd Np l)).trans hl
    rcases h with ⟨ht,hu⟩ | ⟨ht,hu⟩
    · exact ⟨tx,htx,ht ▸ hpv,Np+l.val,hu,hlv⟩
    · exact ⟨tx,htx,ht ▸ hlv,p.val,hu,hpv⟩

lemma normal_form_of_ownership (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop)
    [DecidableRel I] (C : Circuit) (own : List (ℕ × List ℕ))
    (ho : ∀ tx ∈ own, tx.2 ≠ [] ∧
      ((tx.1 < Np ∧ ∀ u ∈ tx.2, Np ≤ u ∧ u < Np+Nl) ∨
      (Np ≤ tx.1 ∧ tx.1 < Np+Nl ∧ ∀ u ∈ tx.2, u < Np)))
    (hc : ∀ p l, I p l ↔ ∃ tx ∈ own,
      (tx.1 = p.val ∧ Np+l.val ∈ tx.2) ∨
      (tx.1 = Np+l.val ∧ p.val ∈ tx.2))
    (hb : (own.map (fun tx => tx.2.length)).sum + own.length - 1 ≤ C.size) :
    ∃ (D : Circuit) (P L : Finset ℕ), IsAO2 (Np+Nl) D ∧
      (∀ z : Fin (Np+Nl) → Bool, circuitFun (Np+Nl) D z =
        decide (∃ p l, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) ∧
      D.size ≤ C.size ∧
      (∀ w ∈ P, w < Np ∨ ∃ i < D.gates.length, w = Np+Nl+i ∧
        (gateAt D i).op = GateOp.or ∧ ∀ u ∈ (gateAt D i).inputs, u ∈ P) ∧
      (∀ w ∈ L, (Np ≤ w ∧ w < Np+Nl) ∨ ∃ i < D.gates.length, w = Np+Nl+i ∧
        (gateAt D i).op = GateOp.or ∧ ∀ u ∈ (gateAt D i).inputs, u ∈ L) ∧
      ∀ i < D.gates.length, (gateAt D i).op = GateOp.and →
        ∃ a b, (gateAt D i).inputs = [a,b] ∧ ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P)) := by
  obtain ⟨P,L,hao,hP,hL,hands⟩ := coverCircuitB_twoLevel Np Nl own (fun tx htx => (ho tx htx).2)
  refine ⟨coverCircuitB (Np+Nl) own,P,L,hao,
    coverCircuitB_incidence Np Nl I own (fun tx htx => (ho tx htx).2) hc,?_,hP,hL,hands⟩
  rwa [coverCircuitB_size_eq (Np+Nl) own (fun tx htx => (ho tx htx).1)]

lemma point_ne_line (Np Nl : ℕ) (p : Fin Np) (l : Fin Nl) :
    Fin.castAdd Nl p ≠ Fin.natAdd Np l := by
  intro h
  have he := congrArg Fin.val h
  have hp := p.isLt
  simp only [Fin.val_castAdd,Fin.val_natAdd] at he
  omega

lemma point_essential (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I]
    (C : Circuit)
    (hfun : ∀ z : Fin (Np+Nl) → Bool, circuitFun (Np+Nl) C z =
      decide (∃ p l, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true))
    (p : Fin Np) (l : Fin Nl) (hI : I p l) :
    ∃ x : Fin (Np+Nl) → Bool,
      circuitFun (Np+Nl) C (Function.update x (Fin.castAdd Nl p) (!x (Fin.castAdd Nl p))) ≠
      circuitFun (Np+Nl) C x := by
  let x : Fin (Np+Nl) → Bool := fun i => decide (i = Fin.natAdd Np l)
  have hx (q : Fin Np) : x (Fin.castAdd Nl q) = false := by
    simp [x,point_ne_line Np Nl q l]
  have old : circuitFun (Np+Nl) C x = false := by
    apply Bool.eq_false_of_not_eq_true
    intro h
    rw [hfun] at h
    obtain ⟨q,s,_,hq,_⟩ := of_decide_eq_true h
    rw [hx q] at hq
    contradiction
  have fresh : circuitFun (Np+Nl) C (Function.update x (Fin.castAdd Nl p) (!x (Fin.castAdd Nl p))) = true := by
    rw [hfun]
    apply decide_eq_true_iff.mpr
    refine ⟨p,l,hI,?_,?_⟩
    · simp [hx p]
    · rw [Function.update_of_ne (point_ne_line Np Nl p l).symm]
      simp [x]
  exact ⟨x,by rw [old,fresh]; decide⟩

lemma line_essential (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I]
    (C : Circuit)
    (hfun : ∀ z : Fin (Np+Nl) → Bool, circuitFun (Np+Nl) C z =
      decide (∃ p l, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true))
    (p : Fin Np) (l : Fin Nl) (hI : I p l) :
    ∃ x : Fin (Np+Nl) → Bool,
      circuitFun (Np+Nl) C (Function.update x (Fin.natAdd Np l) (!x (Fin.natAdd Np l))) ≠
      circuitFun (Np+Nl) C x := by
  let x : Fin (Np+Nl) → Bool := fun i => decide (i = Fin.castAdd Nl p)
  have hx (s : Fin Nl) : x (Fin.natAdd Np s) = false := by
    simp [x,(point_ne_line Np Nl p s).symm]
  have old : circuitFun (Np+Nl) C x = false := by
    apply Bool.eq_false_of_not_eq_true
    intro h
    rw [hfun] at h
    obtain ⟨q,s,_,_,hs⟩ := of_decide_eq_true h
    rw [hx s] at hs
    contradiction
  have fresh : circuitFun (Np+Nl) C (Function.update x (Fin.natAdd Np l) (!x (Fin.natAdd Np l))) = true := by
    rw [hfun]
    apply decide_eq_true_iff.mpr
    refine ⟨p,l,hI,?_,?_⟩
    · rw [Function.update_of_ne (point_ne_line Np Nl p l)]
      simp [x]
    · simp [hx l]
  exact ⟨x,by rw [old,fresh]; decide⟩

lemma owner_vertices_incident (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop)
    [DecidableRel I] (own : List (ℕ × List ℕ))
    (ho : ∀ tx ∈ own, tx.2 ≠ [] ∧
      ((tx.1 < Np ∧ ∀ u ∈ tx.2, Np ≤ u ∧ u < Np+Nl) ∨
      (Np ≤ tx.1 ∧ tx.1 < Np+Nl ∧ ∀ u ∈ tx.2, u < Np)))
    (hc : ∀ p l, I p l ↔ ∃ tx ∈ own,
      (tx.1 = p.val ∧ Np+l.val ∈ tx.2) ∨
      (tx.1 = Np+l.val ∧ p.val ∈ tx.2)) :
    ∀ w ∈ own.flatMap (fun tx => tx.1 :: tx.2),
      ∃ (p : Fin Np) (l : Fin Nl), I p l ∧ (w = p.val ∨ w = Np+l.val) := by
  intro w hw
  obtain ⟨tx,htx,hw⟩ := List.mem_flatMap.mp hw
  obtain ⟨hne,htag⟩ := ho tx htx
  obtain ⟨u,hu,hw⟩ : ∃ u ∈ tx.2, w = tx.1 ∨ w = u := by
    rcases List.mem_cons.mp hw with hw | hw
    · obtain ⟨u,hu⟩ := List.exists_mem_of_ne_nil _ hne
      exact ⟨u,hu,Or.inl hw⟩
    · exact ⟨w,hw,Or.inr rfl⟩
  rcases htag with ⟨ht,hr⟩ | ⟨ht,ht',hr⟩
  · obtain ⟨hul,huh⟩ := hr u hu
    let p : Fin Np := ⟨tx.1,ht⟩
    let l : Fin Nl := ⟨u-Np,by omega⟩
    have he : Np+l.val = u := by dsimp [l]; omega
    refine ⟨p,l,(hc p l).mpr ⟨tx,htx,Or.inl ⟨rfl,he.symm ▸ hu⟩⟩,?_⟩
    simpa only [p,Fin.val_mk,he] using hw
  · have hup := hr u hu
    let p : Fin Np := ⟨u,hup⟩
    let l : Fin Nl := ⟨tx.1-Np,by omega⟩
    have he : Np+l.val = tx.1 := by dsimp [l]; omega
    refine ⟨p,l,(hc p l).mpr ⟨tx,htx,Or.inr ⟨he.symm,hu⟩⟩,?_⟩
    simpa only [p,Fin.val_mk,he] using hw.symm

lemma owner_vertices_length (own : List (ℕ × List ℕ)) :
    (own.flatMap (fun tx => tx.1 :: tx.2)).length =
      (own.map (fun tx => tx.2.length)).sum + own.length := by
  induction own with
  | nil => simp
  | cons tx own ih => simp [ih]; omega

lemma disjoint_owner_support (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop)
    [DecidableRel I] (C : Circuit) (own : List (ℕ × List ℕ))
    (ho : ∀ tx ∈ own, tx.2 ≠ [] ∧
      ((tx.1 < Np ∧ ∀ u ∈ tx.2, Np ≤ u ∧ u < Np+Nl) ∨
      (Np ≤ tx.1 ∧ tx.1 < Np+Nl ∧ ∀ u ∈ tx.2, u < Np)))
    (hc : ∀ p l, I p l ↔ ∃ tx ∈ own,
      (tx.1 = p.val ∧ Np+l.val ∈ tx.2) ∨
      (tx.1 = Np+l.val ∧ p.val ∈ tx.2))
    (hfun : ∀ z : Fin (Np+Nl) → Bool, circuitFun (Np+Nl) C z =
      decide (∃ p l, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true))
    (hn : (own.flatMap (fun tx => tx.1 :: tx.2)).Nodup) :
    ∃ S : Finset (Fin (Np+Nl)),
      S.card = (own.map (fun tx => tx.2.length)).sum + own.length ∧
      ∀ i ∈ S, ∃ x : Fin (Np+Nl) → Bool,
        circuitFun (Np+Nl) C (Function.update x i (!x i)) ≠ circuitFun (Np+Nl) C x := by
  let R := own.flatMap (fun tx => tx.1 :: tx.2)
  let T := R.toFinset
  let S : Finset (Fin (Np+Nl)) := Finset.univ.filter (fun i => i.val ∈ T)
  have hbound : ∀ w ∈ T, w < Np+Nl := by
    intro w hw
    obtain ⟨p,l,_,he⟩ := owner_vertices_incident Np Nl I own ho hc w (List.mem_toFinset.mp hw)
    have hp := p.isLt
    have hl := l.isLt
    rcases he with he | he <;> omega
  have heq : S.image Fin.val = T := by
    ext w
    constructor
    · intro hw
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hw
      exact (Finset.mem_filter.mp hi).2
    · intro hw
      refine Finset.mem_image.mpr ⟨⟨w,hbound w hw⟩,?_,rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hw⟩
  have hcard : S.card = R.length := by
    calc
      S.card = T.card := by rw [← heq,Finset.card_image_of_injective _ Fin.val_injective]
      _ = R.length := List.toFinset_card_of_nodup hn
  refine ⟨S,?_,?_⟩
  · rw [hcard]
    exact owner_vertices_length own
  · intro i hi
    have hiR : i.val ∈ R := List.mem_toFinset.mp (Finset.mem_filter.mp hi).2
    obtain ⟨p,l,hI,he⟩ := owner_vertices_incident Np Nl I own ho hc i.val hiR
    rcases he with he | he
    · have hia : i = Fin.castAdd Nl p := Fin.ext he
      rw [hia]
      exact point_essential Np Nl I C hfun p l hI
    · have hia : i = Fin.natAdd Np l := Fin.ext he
      rw [hia]
      exact line_essential Np Nl I C hfun p l hI

lemma star_forest_budget (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop)
    [DecidableRel I] (C : Circuit) (own : List (ℕ × List ℕ))
    (ho : ∀ tx ∈ own, tx.2 ≠ [] ∧
      ((tx.1 < Np ∧ ∀ u ∈ tx.2, Np ≤ u ∧ u < Np+Nl) ∨
      (Np ≤ tx.1 ∧ tx.1 < Np+Nl ∧ ∀ u ∈ tx.2, u < Np)))
    (hc : ∀ p l, I p l ↔ ∃ tx ∈ own,
      (tx.1 = p.val ∧ Np+l.val ∈ tx.2) ∨
      (tx.1 = Np+l.val ∧ p.val ∈ tx.2))
    (hfun : ∀ z : Fin (Np+Nl) → Bool, circuitFun (Np+Nl) C z =
      decide (∃ p l, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true))
    (hn : (own.flatMap (fun tx => tx.1 :: tx.2)).Nodup)
    (lower : ∀ S : Finset (Fin (Np+Nl)),
      (∀ i ∈ S, ∃ x : Fin (Np+Nl) → Bool,
        circuitFun (Np+Nl) C (Function.update x i (!x i)) ≠ circuitFun (Np+Nl) C x) →
      S.card ≤ C.size+1) :
    (own.map (fun tx => tx.2.length)).sum + own.length - 1 ≤ C.size := by
  obtain ⟨S,hs,hdep⟩ := disjoint_owner_support Np Nl I C own ho hc hfun hn
  have h := lower S hdep
  omega

end PEqualNP.Outside.L_meta_2685_aux

namespace PEqualNP.Outside.L_meta_2685

lemma and_below_linear {α : Type*} (A : Finset α)
    (f g : (α → Bool) → Bool) (hf : Monotone f) (hg : Monotone g)
    (h : ∀ x, (f x && g x) = true → ∃ a ∈ A, x a = true) :
    (∀ x, f x = true → ∃ a ∈ A, x a = true) ∨
      (∀ x, g x = true → ∃ a ∈ A, x a = true) := by
  classical
  by_cases hfA : ∀ x, f x = true → ∃ a ∈ A, x a = true
  · exact Or.inl hfA
  right
  intro y hgy
  by_contra hy
  obtain ⟨x, hx⟩ := not_forall.mp hfA
  obtain ⟨hfx, hx⟩ := not_imp.mp hx
  let z : α → Bool := fun a => x a || y a
  have hxz : x ≤ z := by
    intro a
    change x a ≤ (x a || y a)
    cases x a <;> cases y a <;> decide
  have hyz : y ≤ z := by
    intro a
    change y a ≤ (x a || y a)
    cases x a <;> cases y a <;> decide
  have hfz : f z = true := le_antisymm le_top (hfx ▸ hf hxz)
  have hgz : g z = true := le_antisymm le_top (hgy ▸ hg hyz)
  obtain ⟨a, ha, hza⟩ := h z (by simp only [hfz, hgz, Bool.and_self])
  have hxa : x a = false := by
    cases hxa : x a
    · rfl
    · exact False.elim (hx ⟨a, ha, hxa⟩)
  have hya : y a = false := by
    cases hya : y a
    · rfl
    · exact False.elim (hy ⟨a, ha, hya⟩)
  simp only [z, hxa, hya, Bool.or_self, Bool.false_eq_true] at hza

def oneInput {α : Type*} [DecidableEq α] (a : α) : α → Bool :=
  fun b => decide (b = a)

lemma oneInput_le {α : Type*} [DecidableEq α] {a : α} {x : α → Bool}
    (h : x a = true) : oneInput a ≤ x := by
  intro b
  by_cases hb : b = a
  · subst b
    simp only [oneInput, decide_true, h, le_refl]
  · simp only [oneInput, hb, decide_false, Bool.false_le]

lemma below_linear_singleton {α : Type*} [DecidableEq α] (A : Finset α)
    (f : (α → Bool) → Bool)
    (h : ∀ x, f x = true → ∃ a ∈ A, x a = true)
    {a : α} (ha : f (oneInput a) = true) : a ∈ A := by
  obtain ⟨b, hb, hba⟩ := h (oneInput a) ha
  have : b = a := by simpa only [oneInput, decide_eq_true_eq] using hba
  simpa only [this] using hb

lemma linear_or_singletons {α : Type*} [DecidableEq α] (A : Finset α)
    (f g : (α → Bool) → Bool) (hf : Monotone f) (hg : Monotone g)
    (h : ∀ x, (f x || g x) = true ↔ ∃ a ∈ A, x a = true) :
    ∀ x, (f x || g x) = true ↔
      (∃ a, f (oneInput a) = true ∧ x a = true) ∨ g x = true := by
  intro x
  constructor
  · intro hfg
    obtain ⟨a, ha, hxa⟩ := (h x).mp hfg
    have hp : (f (oneInput a) || g (oneInput a)) = true :=
      (h _).mpr ⟨a, ha, by simp only [oneInput, decide_true]⟩
    rw [Bool.or_eq_true_eq_eq_true_or_eq_true] at hp
    rcases hp with hfa | hga
    · exact Or.inl ⟨a, hfa, hxa⟩
    · exact Or.inr (le_antisymm le_top (hga ▸ hg (oneInput_le hxa)))
  · rintro (⟨a, hfa, hxa⟩ | hgx)
    · rw [Bool.or_eq_true_eq_eq_true_or_eq_true]
      exact Or.inl (le_antisymm le_top (hfa ▸ hf (oneInput_le hxa)))
    · rw [Bool.or_eq_true_eq_eq_true_or_eq_true]
      exact Or.inr hgx

lemma shared_singleton_support {α : Type*} [DecidableEq α] (A B : Finset α)
    (f : (α → Bool) → Bool)
    (hA : ∀ x, f x = true → ∃ a ∈ A, x a = true)
    (hB : ∀ x, f x = true → ∃ a ∈ B, x a = true)
    (hAB : ∀ a ∈ A, ∀ b ∈ A, a ∈ B → b ∈ B → a = b)
    {a b : α} (ha : f (oneInput a) = true) (hb : f (oneInput b) = true) :
    a = b := by
  exact hAB a (below_linear_singleton A f hA ha)
    b (below_linear_singleton A f hA hb)
    (below_linear_singleton B f hB ha) (below_linear_singleton B f hB hb)

lemma eq_of_true_iff (a b : Bool) (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

lemma shared_linear_replace {α β : Type*} [DecidableEq α]
    (A : β → Finset α) (v : (α → Bool) → Bool)
    (h : β → (α → Bool) → Bool) (hv : Monotone v)
    (hh : ∀ k, Monotone (h k))
    (hout : ∀ k x, (v x || h k x) = true ↔ ∃ a ∈ A k, x a = true)
    (i j : β)
    (hij : ∀ a ∈ A i, ∀ b ∈ A i, a ∈ A j → b ∈ A j → a = b) :
    (∀ k x, (v x || h k x) = h k x) ∨
      ∃ a, v (oneInput a) = true ∧
        ∀ k x, (v x || h k x) = (x a || h k x) := by
  classical
  have hbelow (k : β) : ∀ x, v x = true → ∃ a ∈ A k, x a = true := by
    intro x hx
    apply (hout k x).mp
    simp only [hx, Bool.true_or]
  have unique {a b : α} (ha : v (oneInput a) = true)
      (hb : v (oneInput b) = true) : a = b :=
    shared_singleton_support (A i) (A j) v (hbelow i) (hbelow j) hij ha hb
  by_cases hs : ∃ a, v (oneInput a) = true
  · obtain ⟨a, ha⟩ := hs
    right
    refine ⟨a, ha, ?_⟩
    intro k x
    apply eq_of_true_iff
    rw [linear_or_singletons (A k) v (h k) hv (hh k) (hout k) x,
      Bool.or_eq_true_eq_eq_true_or_eq_true]
    apply or_congr _ Iff.rfl
    constructor
    · rintro ⟨b, hb, hxb⟩
      simpa only [unique hb ha] using hxb
    · intro hxa
      exact ⟨a, ha, hxa⟩
  · left
    intro k x
    apply eq_of_true_iff
    rw [linear_or_singletons (A k) v (h k) hv (hh k) (hout k) x]
    constructor
    · rintro (⟨a, ha, _⟩ | hkx)
      · exact False.elim (hs ⟨a, ha⟩)
      · exact hkx
    · exact Or.inr

end PEqualNP.Outside.L_meta_2685

namespace PEqualNP.Outside.L_meta_2685

lemma empty_incidence (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I]
    (C : PEqualNP.CircuitLowerBounds.Circuit) (hI : ∀ p l, ¬ I p l) :
    ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (P L : Finset ℕ), PEqualNP.TopForm.IsAO2 (Np + Nl) D ∧ (∀ y : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) D y = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ y (Fin.castAdd Nl p) = true ∧ y (Fin.natAdd Np l) = true)) ∧ D.size ≤ C.size ∧ (∀ w ∈ P, w < Np ∨ ∃ i < D.gates.length, w = Np + Nl + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs, u ∈ P) ∧ (∀ w ∈ L, (Np ≤ w ∧ w < Np + Nl) ∨ ∃ i < D.gates.length, w = Np + Nl + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs, u ∈ L) ∧ ∀ i < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ a b : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs = [a, b] ∧ ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P)) := by
  refine ⟨⟨[], Np + Nl⟩, ∅, ∅, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [PEqualNP.TopForm.IsAO2, PEqualNP.EdgeOwnership.AndOrOnly,
      PEqualNP.MetaComplexity.NestedCover.ReadsBack]
  · intro y
    simp [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval,
      PEqualNP.CircuitLowerBounds.Circuit.wires, hI]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · simp
  · simp
  · simp

lemma monotone_eq_of_hypergraph_boundary {α : Type} [Fintype α] [DecidableEq α]
    (E : Finset (Finset α)) (f : Finset α → Bool)
    (mono : ∀ S T, S ⊆ T → f S ≤ f T)
    (positive : ∀ e ∈ E, f e = true)
    (negative : ∀ T, (∀ e ∈ E, ¬ e ⊆ T) →
      (∀ a, a ∉ T → ∃ e ∈ E, e ⊆ insert a T) → f T = false)
    (S : Finset α) : f S = decide (∃ e ∈ E, e ⊆ S) := by
  classical
  by_cases h : ∃ e ∈ E, e ⊆ S
  · obtain ⟨e, he, hs⟩ := h
    have hm := mono e S hs
    have ht : f S = true := by
      cases hfs : f S with
      | false =>
        have hn : ¬ ((true : Bool) ≤ false) := by decide
        exact False.elim (hn (by simpa [positive e he, hfs] using hm))
      | true => rfl
    simp [ht, show ∃ e ∈ E, e ⊆ S from ⟨e, he, hs⟩]
  · let A : Finset (Finset α) := Finset.univ.filter fun T =>
      S ⊆ T ∧ ∀ e ∈ E, ¬ e ⊆ T
    have hs : ∀ e ∈ E, ¬ e ⊆ S := fun e he hsub => h ⟨e, he, hsub⟩
    have hmem : S ∈ A := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (fun _ ha => ha), hs⟩
    obtain ⟨T, hT, hmax⟩ := Finset.exists_max_image A Finset.card ⟨S, hmem⟩
    have hST : S ⊆ T := (Finset.mem_filter.mp hT).2.1
    have hfree : ∀ e ∈ E, ¬ e ⊆ T := (Finset.mem_filter.mp hT).2.2
    have hboundary : ∀ a, a ∉ T → ∃ e ∈ E, e ⊆ insert a T := by
      intro a ha
      by_contra hn
      have hfree' : ∀ e ∈ E, ¬ e ⊆ insert a T := fun e he hsub => hn ⟨e, he, hsub⟩
      have hmem' : insert a T ∈ A := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, hST.trans (Finset.subset_insert _ _), hfree'⟩
      have hcard := hmax (insert a T) hmem'
      simp [Finset.card_insert_of_notMem ha] at hcard
    have hn := negative T hfree hboundary
    have hf : f S = false := by
      cases hfs : f S with
      | false => rfl
      | true =>
        have hbad : ¬ ((true : Bool) ≤ false) := by decide
        exact False.elim (hbad (by simpa [hn, hfs] using mono S T hST))
    simp [h, hf]

end PEqualNP.Outside.L_meta_2685

namespace PEqualNP.Outside.L_meta_2685.EliminationRoute

lemma leaf_zero {Np Nl : ℕ} (I : Fin Np → Fin Nl → Prop) [DecidableRel I]
    (p0 : Fin Np) (x : Fin Np → Bool) (y : Fin Nl → Bool) :
    decide (∃ p l, I p l ∧ Function.update x p0 false p = true ∧ y l = true) =
      decide (∃ p l, I p l ∧ p ≠ p0 ∧ x p = true ∧ y l = true) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨p, l, hp, hx, hy⟩
    have hne : p ≠ p0 := by
      rintro rfl
      simp at hx
    exact ⟨p, l, hp, hne, by simpa [Function.update_of_ne hne] using hx, hy⟩
  · rintro ⟨p, l, hp, hne, hx, hy⟩
    exact ⟨p, l, hp, by simpa [Function.update_of_ne hne] using hx, hy⟩

lemma leaf_one {Np Nl : ℕ} (I : Fin Np → Fin Nl → Prop) [DecidableRel I]
    (p0 : Fin Np) (l0 : Fin Nl) (edge : I p0 l0)
    (leaf : ∀ l, I p0 l → l = l0) (x : Fin Np → Bool) (y : Fin Nl → Bool) :
    decide (∃ p l, I p l ∧ Function.update x p0 true p = true ∧ y l = true) =
      (y l0 || decide (∃ p l, I p l ∧ l ≠ l0 ∧ x p = true ∧ y l = true)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, Bool.or_eq_true]
  constructor
  · rintro ⟨p, l, hp, hx, hy⟩
    by_cases hl : l = l0
    · exact Or.inl (hl ▸ hy)
    · right
      have hne : p ≠ p0 := by
        rintro rfl
        exact hl (leaf l hp)
      exact ⟨p, l, hp, hl, by simpa [Function.update_of_ne hne] using hx, hy⟩
  · rintro (hy | ⟨p, l, hp, hl, hx, hy⟩)
    · exact ⟨p0, l0, edge, by simp, hy⟩
    · have hne : p ≠ p0 := by
        rintro rfl
        exact hl (leaf l hp)
      exact ⟨p, l, hp, by simpa [Function.update_of_ne hne] using hx, hy⟩

lemma duplicate_leaf_cover {Np Nl : ℕ} (I : Fin Np → Fin Nl → Prop)
    (p0 p1 : Fin Np) (l0 : Fin Nl) (distinct : p0 ≠ p1)
    (edge : I p1 l0) (leaf0 : ∀ l, I p0 l → l = l0)
    (leaf1 : ∀ l, I p1 l → l = l0)
    (A : Finset (Fin Np)) (B : Finset (Fin Nl))
    (cover : ∀ p l, I p l → p ≠ p0 → p ∈ A ∨ l ∈ B) :
    ∃ (A' : Finset (Fin Np)) (B' : Finset (Fin Nl)),
      (∀ p l, I p l → p ∈ A' ∨ l ∈ B') ∧
      A'.card + B'.card ≤ A.card + B.card := by
  classical
  by_cases hb : l0 ∈ B
  · refine ⟨A, B, ?_, le_rfl⟩
    intro p l hp
    by_cases h : p = p0
    · exact Or.inr ((leaf0 l (h ▸ hp)) ▸ hb)
    · exact cover p l hp h
  · have ha : p1 ∈ A := (cover p1 l0 edge distinct.symm).resolve_right hb
    refine ⟨A.erase p1, insert l0 B, ?_, ?_⟩
    · intro p l hp
      by_cases hp0 : p = p0
      · right
        have h := leaf0 l (hp0 ▸ hp)
        simp [h]
      by_cases hp1 : p = p1
      · right
        have h := leaf1 l (hp1 ▸ hp)
        simp [h]
      rcases cover p l hp hp0 with h | h
      · exact Or.inl (Finset.mem_erase.mpr ⟨hp1, h⟩)
      · exact Or.inr (Finset.mem_insert_of_mem h)
    · have he := Finset.card_erase_add_one ha
      rw [Finset.card_insert_of_notMem hb]
      omega


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

noncomputable def inputSupport {n : ℕ} (f : (Fin n → Bool) → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun i => ∃ x, f (Function.update x i (!x i)) ≠ f x

lemma mem_inputSupport {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n) :
    i ∈ inputSupport f ↔ ∃ x, f (Function.update x i (!x i)) ≠ f x := by
  classical
  simp [inputSupport]

lemma support_family_update {α : Type} [DecidableEq α] (R : ℕ → Finset α)
    (k : ℕ) (bound : ∀ S : Finset ℕ, (S.biUnion R).card ≤ k + S.card)
    (w : ℕ) (T : Finset ℕ) (B : Finset α)
    (hT : T.card ≤ 2) (hB : B ⊆ T.biUnion R) (S : Finset ℕ) :
    (S.biUnion (Function.update R w B)).card ≤ k + 1 + S.card := by
  classical
  by_cases hw : w ∈ S
  · have sub : S.biUnion (Function.update R w B) ⊆ (S.erase w ∪ T).biUnion R := by
      intro i hi
      obtain ⟨v, hv, hi⟩ := Finset.mem_biUnion.mp hi
      by_cases hvw : v = w
      · subst v
        simp only [Function.update_self] at hi
        obtain ⟨v, hv, hi⟩ := Finset.mem_biUnion.mp (hB hi)
        exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_union_right _ hv, hi⟩
      · rw [Function.update_of_ne hvw] at hi
        exact Finset.mem_biUnion.mpr
          ⟨v, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hvw, hv⟩), hi⟩
    have hcard := Finset.card_le_card sub
    have hbound := bound (S.erase w ∪ T)
    have hunion := Finset.card_union_le (S.erase w) T
    have herase := Finset.card_erase_add_one hw
    omega
  · have eq : S.biUnion (Function.update R w B) = S.biUnion R := by
      apply Finset.biUnion_congr rfl
      intro v hv
      have hvw : v ≠ w := by
        rintro rfl
        exact hw hv
      exact Function.update_of_ne hvw _ _
    rw [eq]
    have := bound S
    omega

lemma fold_wires_length (gs : List Gate) (x : List Bool) :
    (gs.foldl (fun vs g => vs ++ [g.op.eval (g.inputs.map fun w => vs.getD w false)]) x).length =
      x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]
    simp
    omega

lemma getD_append_one (xs : List Bool) (b : Bool) (w : ℕ) :
    (xs ++ [b]).getD w false = if w = xs.length then b else xs.getD w false := by
  induction xs generalizing w with
  | nil => cases w <;> simp
  | cons a xs ih => cases w <;> simp_all

noncomputable def wireSupport (n : ℕ) (gs : List Gate) (w : ℕ) : Finset (Fin n) :=
  inputSupport (circuitFun n ⟨gs, w⟩)

def nextValue (n : ℕ) (gs : List Gate) (g : Gate) (x : Fin n → Bool) : Bool :=
  g.op.eval (g.inputs.map fun w => circuitFun n ⟨gs, w⟩ x)

lemma circuitFun_append (n : ℕ) (gs : List Gate) (g : Gate) (w : ℕ) (x : Fin n → Bool) :
    circuitFun n ⟨gs ++ [g], w⟩ x =
      if w = n + gs.length then nextValue n gs g x else circuitFun n ⟨gs, w⟩ x := by
  simp only [circuitFun, Circuit.eval, Circuit.wires, List.foldl_append,
    List.foldl_cons, List.foldl_nil, getD_append_one, fold_wires_length, List.length_ofFn]
  rfl

lemma wireSupport_append (n : ℕ) (gs : List Gate) (g : Gate) :
    wireSupport n (gs ++ [g]) =
      Function.update (wireSupport n gs) (n + gs.length) (inputSupport (nextValue n gs g)) := by
  classical
  funext w
  by_cases hw : w = n + gs.length
  · subst w
    simp only [Function.update_self, wireSupport]
    congr 1
    funext x
    simp [circuitFun_append]
  · rw [Function.update_of_ne hw]
    unfold wireSupport
    congr 1
    funext x
    simp [circuitFun_append, hw]

lemma nextValue_support (n : ℕ) (gs : List Gate) (g : Gate) :
    inputSupport (nextValue n gs g) ⊆ g.inputs.toFinset.biUnion (wireSupport n gs) := by
  classical
  intro i hi
  obtain ⟨x, hx⟩ := (mem_inputSupport _ _).mp hi
  by_contra hn
  have hagree : ∀ w ∈ g.inputs,
      circuitFun n ⟨gs, w⟩ (Function.update x i (!x i)) = circuitFun n ⟨gs, w⟩ x := by
    intro w hw
    have hnot : i ∉ wireSupport n gs w := by
      intro hs
      exact hn (Finset.mem_biUnion.mpr ⟨w, List.mem_toFinset.mpr hw, hs⟩)
    apply Classical.byContradiction
    intro h
    exact hnot ((mem_inputSupport _ _).mpr ⟨x, h⟩)
  apply hx
  unfold nextValue
  congr 1
  exact List.map_congr_left hagree

lemma empty_support_mem (n w : ℕ) (i : Fin n) (hi : i ∈ wireSupport n [] w) :
    i.val = w := by
  classical
  obtain ⟨x, hx⟩ := (mem_inputSupport _ _).mp hi
  by_contra hne
  apply hx
  simp only [circuitFun, Circuit.eval, Circuit.wires, List.foldl_nil,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split
  · rename_i hw
    have h : (⟨w, hw⟩ : Fin n) ≠ i := by
      intro he
      exact hne (congrArg Fin.val he).symm
    simp [Function.update_of_ne h]
  · rfl

lemma support_family_bound (n : ℕ) (gs : List Gate)
    (fanin : ∀ g ∈ gs, g.inputs.length ≤ 2) (S : Finset ℕ) :
    (S.biUnion (wireSupport n gs)).card ≤ gs.length + S.card := by
  classical
  induction gs using List.reverseRecOn generalizing S with
  | nil =>
    simp only [List.length_nil, Nat.zero_add]
    apply Finset.card_le_card_of_injOn (fun i : Fin n => i.val)
    · intro i hi
      obtain ⟨w, hw, hi⟩ := Finset.mem_biUnion.mp hi
      change i.val ∈ S
      rw [empty_support_mem n w i hi]
      exact hw
    · intro i hi j hj h
      exact Fin.ext h
  | append_singleton gs g ih =>
    have hgs : ∀ a ∈ gs, a.inputs.length ≤ 2 := by
      intro a ha
      exact fanin a (List.mem_append.mpr (Or.inl ha))
    have hg : g.inputs.length ≤ 2 := fanin g (by simp)
    rw [wireSupport_append]
    have := support_family_update (wireSupport n gs) gs.length (ih hgs)
      (n + gs.length) g.inputs.toFinset (inputSupport (nextValue n gs g))
      (le_trans (List.toFinset_card_le g.inputs) hg) (nextValue_support n gs g) S
    simpa using this

lemma essential_card_le_size (n : ℕ) (C : Circuit)
    (fanin : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (S : Finset (Fin n))
    (hS : ∀ i ∈ S, ∃ x : Fin n → Bool,
      circuitFun n C (Function.update x i (!x i)) ≠ circuitFun n C x) :
    S.card ≤ C.size + 1 := by
  classical
  have sub : S ⊆ wireSupport n C.gates C.output := by
    intro i hi
    exact (mem_inputSupport _ _).mpr (hS i hi)
  have hb := support_family_bound n C.gates fanin {C.output}
  simpa only [Finset.singleton_biUnion, Finset.card_singleton, Circuit.size] using
    (Finset.card_le_card sub).trans (by simpa using hb)

end PEqualNP.Outside.L_meta_2685.EliminationRoute

namespace PEqualNP.Outside.L_meta_2685

lemma star_forest_normal_form (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop)
    [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit)
    (ao : PEqualNP.TopForm.IsAO2 (Np + Nl) C)
    (correct : ∀ z : Fin (Np + Nl) → Bool,
      PEqualNP.MetaComplexity.circuitFun (Np + Nl) C z =
        decide (∃ p l, I p l ∧ z (Fin.castAdd Nl p) = true ∧
          z (Fin.natAdd Np l) = true))
    (own : List (ℕ × List ℕ))
    (tagged : ∀ tx ∈ own, tx.2 ≠ [] ∧
      ((tx.1 < Np ∧ ∀ u ∈ tx.2, Np ≤ u ∧ u < Np + Nl) ∨
        (Np ≤ tx.1 ∧ tx.1 < Np + Nl ∧ ∀ u ∈ tx.2, u < Np)))
    (covered : ∀ p l, I p l ↔ ∃ tx ∈ own,
      (tx.1 = p.val ∧ Np + l.val ∈ tx.2) ∨
        (tx.1 = Np + l.val ∧ p.val ∈ tx.2))
    (disjoint : (own.flatMap (fun tx => tx.1 :: tx.2)).Nodup) :
    ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (P L : Finset ℕ), PEqualNP.TopForm.IsAO2 (Np + Nl) D ∧ (∀ y : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) D y = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ y (Fin.castAdd Nl p) = true ∧ y (Fin.natAdd Np l) = true)) ∧ D.size ≤ C.size ∧ (∀ w ∈ P, w < Np ∨ ∃ i < D.gates.length, w = Np + Nl + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs, u ∈ P) ∧ (∀ w ∈ L, (Np ≤ w ∧ w < Np + Nl) ∨ ∃ i < D.gates.length, w = Np + Nl + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs, u ∈ L) ∧ ∀ i < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ a b : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs = [a, b] ∧ ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P)) := by
  apply PEqualNP.Outside.L_meta_2685_aux.normal_form_of_ownership Np Nl I C own tagged covered
  apply PEqualNP.Outside.L_meta_2685_aux.star_forest_budget Np Nl I C own tagged covered correct disjoint
  intro S hS
  apply EliminationRoute.essential_card_le_size (Np + Nl) C _ S hS
  intro g hg
  exact (ao.2.2 g hg).le

end PEqualNP.Outside.L_meta_2685
