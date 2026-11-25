import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2448_aux.foundation

namespace M1501
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
end M1501
theorem thm_1501 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
  G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C →
    ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsLeastAO G C' ∧ C'.size = C.size ∧
      (PEqualNP.TopForm.junk G C').card = (PEqualNP.TopForm.junk G C).card ∧ PEqualNP.TopForm.TopForm G C' := by
  intro n G _ C hG hC
  exact PEqualNP.Outside.L_meta_2448_aux.foundation.M1501.main_ind n G hG _ C hC rfl

namespace M1528
namespace P1
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
namespace S90
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl
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
      · rw [if_pos hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact getD_ge w i (by omega)
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
    · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [if_neg hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩
lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
    · rw [if_neg hlt] at h'; cases h'
  · intro h i hi
    rw [if_pos (h i hi).1]; exact (h i hi).2
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
open PEqualNP.EdgeOwnership in
lemma pairInput_left {n : ℕ} (u v : Fin n) : pairInput u v u = true := by
  simp [pairInput]
open PEqualNP.EdgeOwnership in
lemma pairInput_right {n : ℕ} (u v : Fin n) : pairInput u v v = true := by
  simp [pairInput]
open PEqualNP.EdgeOwnership in
lemma pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
  simp [pairInput]
open PEqualNP.EdgeOwnership in
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
open PEqualNP.EdgeOwnership in
lemma reach_var_val {n : ℕ} {C : Circuit} (x : Fin n → Bool) (p : ℕ) (t : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p t.val) (ht : x t = true) :
    val C (List.ofFn x) p = true :=
  orStep_up (n := n) (by simp) hr (by rw [val_ofFn]; exact ht)
open PEqualNP.EdgeOwnership in
lemma side_adj {n : ℕ} (G : SimpleGraph (Fin n)) {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hF : ∀ u v : Fin n, F (pairInput u v) = true → G.Adj u v)
    (a : ℕ) (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and)
    (hbel : ∀ x : Fin n → Bool, val C (List.ofFn x) (n + a) = true → F x = true)
    (p q : ℕ) (hin : (gateAt C a).inputs = [p, q]) (hp : p < n + a) (hq : q < n + a)
    (u v : Fin n) (hu : Relation.ReflTransGen (OrStep n C) p u.val)
    (hv : Relation.ReflTransGen (OrStep n C) q v.val) : G.Adj u v := by
  apply hF
  apply hbel
  rw [val_and (n := n) (by simp) ha hop, hin]
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact ⟨hp, reach_var_val _ _ u hu (pairInput_left u v)⟩
  · exact ⟨hq, reach_var_val _ _ v hv (pairInput_right u v)⟩
open PEqualNP.EdgeOwnership
open PEqualNP.CleanedNonEdge
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
open PEqualNP.TopForm in
lemma top_facts {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : NoFourCycle G) (hL : IsLeastAO G C) (a : ℕ) (ha : a ∈ tops G C) :
    Disjoint (side (n := n) C a 0) (side (n := n) C a 1) ∧
    (∀ u ∈ side (n := n) C a 0, ∀ v ∈ side (n := n) C a 1, G.Adj u v) ∧
    ((side (n := n) C a 0).card ≤ 1 ∨ (side (n := n) C a 1).card ≤ 1) := by
  obtain ⟨⟨hAO, hRB, h2⟩, hfun, _⟩ := hL
  simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha
  obtain ⟨halen, hop, hbel⟩ := ha
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 _ (gateAt_mem halen))
  have hp : p < n + a := hRB a halen p (by rw [hin]; simp)
  have hq : q < n + a := hRB a halen q (by rw [hin]; simp)
  have e0 : opnd C a 0 = p := by simp [opnd, hin]
  have e1 : opnd C a 1 = q := by simp [opnd, hin]
  have hadj : ∀ u ∈ side (n := n) C a 0, ∀ v ∈ side (n := n) C a 1, G.Adj u v := by
    intro u hu v hv
    simp only [side, e0] at hu
    simp only [side, e1] at hv
    exact side_adj G (graphFun G ∅) (fun u v h => (graphFun_pair G u v).mp h) a halen hop hbel
      p q hin hp hq u v (mem_orIn_reach u hu) (mem_orIn_reach v hv)
  refine ⟨?_, hadj, ?_⟩
  · rw [Finset.disjoint_left]
    intro u hu hv
    exact G.irrefl (hadj u hu u hv)
  · by_contra hcon
    simp only [not_or, not_le] at hcon
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hcon.1
    have hsub : side (n := n) C a 1 ⊆ Finset.univ.filter (fun w => G.Adj x w ∧ G.Adj y w) := by
      intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hadj x hx w hw, hadj y hy w hw⟩
    have h5 := Finset.card_le_card hsub
    have h6 := h4 x y hxy
    omega
end S90
namespace S98
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership
def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl
lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega
lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
lemma wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq_foldl, foldl_stepWire_length, List.length_ofFn]
def shiftDown (wOld u : ℕ) : ℕ :=
  if wOld < u then u - 1 else u
def wiresMatch (w0 : List Bool) (bOld : Bool) (wC wD : List Bool) : Prop :=
  wC.length = wD.length + 1 ∧
  w0.length ≤ wD.length ∧
  wC.getD w0.length false = bOld ∧
  (∀ u, u < w0.length → wD.getD u false = w0.getD u false) ∧
  (∀ u, u < w0.length → wC.getD u false = w0.getD u false) ∧
  (∀ u, w0.length < u → wD.getD (u - 1) false = wC.getD u false)
lemma wiresMatch_init (w0 : List Bool) (bOld : Bool) :
    wiresMatch w0 bOld (w0 ++ [bOld]) w0 := by
  refine ⟨by simp, le_rfl, ?_, fun _ _ => rfl, ?_, ?_⟩
  · simp [List.getD_eq_getElem?_getD]
  · intro u hu
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hu]
  · intro u hu
    have h1 : w0.length ≤ u - 1 := by omega
    have h2 : (w0 ++ [bOld]).length ≤ u := by simp; omega
    rw [getD_ge_length w0 (u - 1) h1, getD_ge_length (w0 ++ [bOld]) u h2]
lemma wiresMatch_step {w0 : List Bool} {bOld : Bool} {wC wD : List Bool} {b : Bool}
    (hm : wiresMatch w0 bOld wC wD) :
    wiresMatch w0 bOld (wC ++ [b]) (wD ++ [b]) := by
  obtain ⟨hlen, hle, hbold, hltD, hltC, hgt⟩ := hm
  refine ⟨by simp; omega, by simp; omega, ?_, ?_, ?_, ?_⟩
  · have hlt : w0.length < wC.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
    simpa [List.getD_eq_getElem?_getD] using hbold
  · intro u hu
    have h1 : u < wD.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h1]
    simpa [List.getD_eq_getElem?_getD] using hltD u hu
  · intro u hu
    have h2 : u < wC.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h2]
    simpa [List.getD_eq_getElem?_getD] using hltC u hu
  · intro u hu
    by_cases h1 : u - 1 < wD.length
    · have h2 : u < wC.length := by omega
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_left h1, List.getElem?_append_left h2]
      simpa [List.getD_eq_getElem?_getD] using hgt u hu
    · by_cases heq : u - 1 = wD.length
      · have heqC : u = wC.length := by omega
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, heq, heqC,
            List.getElem?_append_right le_rfl, List.getElem?_append_right le_rfl]
        simp
      · have hg1 : (wD ++ [b]).length ≤ u - 1 := by simp; omega
        have hg2 : (wC ++ [b]).length ≤ u := by simp; omega
        rw [getD_ge_length _ _ hg1, getD_ge_length _ _ hg2]
lemma wiresMatch_getD_shiftDown {w0 : List Bool} {bOld : Bool} {wC wD : List Bool}
    (hm : wiresMatch w0 bOld wC wD) {u : ℕ} (hne : u ≠ w0.length) :
    wD.getD (shiftDown w0.length u) false = wC.getD u false := by
  unfold shiftDown
  by_cases hgt : w0.length < u
  · simp only [hgt, ↓reduceIte]; exact hm.2.2.2.2.2 u hgt
  · simp only [hgt, ↓reduceIte]
    have hlt : u < w0.length := by omega
    rw [hm.2.2.2.1 u hlt, hm.2.2.2.2.1 u hlt]
lemma foldl_wiresMatch (w0 : List Bool) (bOld : Bool) (gsC gsD : List Gate)
    (wC wD : List Bool) (hm : wiresMatch w0 bOld wC wD) (hlen : gsD.length = gsC.length)
    (hstep : ∀ (t : ℕ) (htC : t < gsC.length) (htD : t < gsD.length) (vC vD : List Bool),
      wiresMatch w0 bOld vC vD → vD.length = wD.length + t →
      (gsD[t]'htD).op.eval ((gsD[t]'htD).inputs.map fun i => vD.getD i false) =
      (gsC[t]'htC).op.eval ((gsC[t]'htC).inputs.map fun i => vC.getD i false)) :
    wiresMatch w0 bOld (gsC.foldl stepWire wC) (gsD.foldl stepWire wD) := by
  induction gsC generalizing gsD wC wD with
  | nil =>
    cases gsD with
    | nil => exact hm
    | cons => simp at hlen
  | cons gC restC ih =>
    cases gsD with
    | nil => simp at hlen
    | cons gD restD =>
      simp only [List.foldl_cons]
      have heq0 := hstep 0 (by simp) (by simp) wC wD hm (by simp)
      simp only [List.getElem_cons_zero] at heq0
      have hm1 : wiresMatch w0 bOld (stepWire wC gC) (stepWire wD gD) := by
        unfold stepWire
        rw [heq0]
        exact wiresMatch_step hm
      apply ih restD (stepWire wC gC) (stepWire wD gD) hm1 (by simp at hlen; omega)
      intro t htC htD vC vD hmv hvlen
      have h' := hstep (t + 1) (by simp; omega) (by simp; omega) vC vD hmv
        (by simp [stepWire] at hvlen ⊢; omega)
      simpa only [List.getElem_cons_succ] using h'
lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]
def aliasWire (wOld wNew u : ℕ) : ℕ :=
  if u = wOld then wNew else shiftDown wOld u
def aliasGate (wOld wNew : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (aliasWire wOld wNew)⟩
def W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false
def eraseC (n : ℕ) (C : Circuit) (j i : ℕ) : Circuit :=
  ⟨C.gates.take j ++ (C.gates.drop (j + 1)).map (aliasGate (n + j) i),
    aliasWire (n + j) i C.output⟩
def appOr (n : ℕ) (C : Circuit) (a b : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨GateOp.or, [a, b]⟩], n + C.gates.length⟩
def truncC (C : Circuit) (m : ℕ) : Circuit :=
  ⟨C.gates.take m, C.output⟩
lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]
lemma erase_wires (n : ℕ) (C : Circuit) (j i : ℕ) (hj : j < C.gates.length) (hi : i < n + j)
    (x : Fin n → Bool)
    (h : W n C x i = W n C x (n + j) ∨
      ∀ k, j < k → k < C.gates.length → n + j ∉ (gateAt C k).inputs) :
    ∀ u, (u = n + j → W n C x i = W n C x (n + j)) →
      W n (eraseC n C j i) x (aliasWire (n + j) i u) = W n C x u := by
  obtain ⟨pre, post, gj, hgs, hpre_len, _⟩ := split_gates C.gates j hj
  have hlenC : C.gates.length = pre.length + 1 + post.length := by
    have := congrArg List.length hgs; simp at this; omega
  have htake : C.gates.take j = pre := by rw [hgs, ← hpre_len]; simp
  have hdrop : C.gates.drop (j + 1) = post := by rw [hgs, ← hpre_len]; simp
  intro u hu
  simp only [W, eraseC, wires_eq_foldl, htake, hdrop]
  conv_rhs => rw [hgs, List.foldl_append, List.foldl_cons]
  rw [List.foldl_append]
  let w0 := pre.foldl stepWire (List.ofFn x)
  have hw0_len : w0.length = n + j := by
    simp [w0, foldl_stepWire_length, hpre_len]
  let bOld := gj.op.eval (gj.inputs.map fun k => w0.getD k false)
  have hCi : W n C x i = w0.getD i false := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append]
    exact foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)
  have hCj : W n C x (n + j) = bOld := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + j) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, hw0_len, bOld]
  have hm0 : wiresMatch w0 bOld (stepWire w0 gj) w0 := wiresMatch_init w0 bOld
  have halias_get : ∀ (vC vD : List Bool), wiresMatch w0 bOld vC vD →
      ∀ u, (u = n + j → W n C x i = W n C x (n + j)) →
        vD.getD (aliasWire (n + j) i u) false = vC.getD u false := by
    intro vC vD hmv u hu'
    unfold aliasWire
    by_cases hu : u = n + j
    · have hval_eq : w0.getD i false = bOld := by rw [← hCi, ← hCj]; exact hu' hu
      subst hu
      simp only [↓reduceIte]
      rw [hmv.2.2.2.1 i (by omega), hval_eq, ← hw0_len, hmv.2.2.1]
    · simp only [hu, ↓reduceIte]
      rw [← hw0_len]
      exact wiresMatch_getD_shiftDown hmv (by omega)
  have hmEnd : wiresMatch w0 bOld (post.foldl stepWire (stepWire w0 gj))
      ((post.map (aliasGate (n + j) i)).foldl stepWire w0) := by
    refine foldl_wiresMatch w0 bOld post (post.map (aliasGate (n + j) i)) (stepWire w0 gj) w0 hm0
      (by simp) ?_
    intro t htC htD vC vD hmv _
    simp only [List.getElem_map, aliasGate, List.map_map]
    congr 1
    refine List.map_congr_left fun u hu => ?_
    refine halias_get vC vD hmv u ?_
    intro hun
    rcases h with h | h
    · exact h
    · exfalso
      have hget : gateAt C (j + 1 + t) = post[t] := by
        rw [gateAt_eq C (j + 1 + t) (by omega)]
        have h1 : (pre ++ gj :: post)[j + 1 + t]'(by rw [← hgs]; omega) = post[t]'htC := by
          rw [List.getElem_append_right (by omega)]
          have hsub : j + 1 + t - pre.length = t + 1 := by omega
          simp [hsub]
        simpa [hgs] using h1
      exact h (j + 1 + t) (by omega) (by omega) (by rw [hget, ← hun]; exact hu)
  exact halias_get _ _ hmEnd u hu
lemma erase_length (n : ℕ) (C : Circuit) (j i : ℕ) (hj : j < C.gates.length) :
    (eraseC n C j i).gates.length + 1 = C.gates.length := by
  simp [eraseC]; omega
lemma erase_gateAt_lt (n : ℕ) (C : Circuit) (j i k : ℕ) (hj : j < C.gates.length) (hk : k < j) :
    gateAt (eraseC n C j i) k = gateAt C k := by
  simp only [gateAt, eraseC, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simp; omega)]
  simp [hk]
lemma erase_gateAt_ge (n : ℕ) (C : Circuit) (j i k : ℕ) (hj : j < C.gates.length) (hk : j ≤ k)
    (hk2 : k + 1 < C.gates.length) :
    gateAt (eraseC n C j i) k = aliasGate (n + j) i (gateAt C (k + 1)) := by
  simp only [gateAt, eraseC, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp; omega)]
  have h1 : (List.take j C.gates).length = j := by simp; omega
  have h2 : j + 1 + (k - j) = k + 1 := by omega
  rw [h1, List.getElem?_map, List.getElem?_drop, h2, List.getElem?_eq_getElem hk2]
  rfl
lemma prefix_W (n : ℕ) (pre rest1 rest2 : List Gate) (o1 o2 : ℕ) (x : Fin n → Bool) (u : ℕ)
    (hu : u < n + pre.length) :
    W n ⟨pre ++ rest1, o1⟩ x u = W n ⟨pre ++ rest2, o2⟩ x u := by
  simp only [W, wires_eq_foldl, List.foldl_append]
  have h : u < (pre.foldl stepWire (List.ofFn x)).length := by
    rw [foldl_stepWire_length]; simpa using hu
  rw [foldl_stepWire_getD_lt rest1 (pre.foldl stepWire (List.ofFn x)) u h,
    foldl_stepWire_getD_lt rest2 (pre.foldl stepWire (List.ofFn x)) u h]
lemma erase_W_lt (n : ℕ) (C : Circuit) (j i : ℕ) (hj : j < C.gates.length) (x : Fin n → Bool)
    (u : ℕ) (hu : u < n + j) : W n (eraseC n C j i) x u = W n C x u := by
  have h := prefix_W n (C.gates.take j) ((C.gates.drop (j + 1)).map (aliasGate (n + j) i))
    (C.gates.drop j) (aliasWire (n + j) i C.output) C.output x u
    (by rw [List.length_take]; omega)
  have e2 : (⟨C.gates.take j ++ C.gates.drop j, C.output⟩ : Circuit) = C := by
    cases C; simp
  rw [e2] at h
  exact h
lemma appOr_W_lt (n : ℕ) (C : Circuit) (a b : ℕ) (x : Fin n → Bool) (u : ℕ)
    (hu : u < n + C.gates.length) : W n (appOr n C a b) x u = W n C x u := by
  have h := prefix_W n C.gates [⟨GateOp.or, [a, b]⟩] [] (n + C.gates.length) C.output x u hu
  have e2 : (⟨C.gates ++ [], C.output⟩ : Circuit) = C := by
    cases C; simp
  rw [e2] at h
  exact h
lemma W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, foldl_stepWire_length, hpre_len]
  have hCj : W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + k) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append]
    exact (foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact getD_ge_length w0 i (by omega)
lemma W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    W n C x u = x ⟨u, hu⟩ := by
  simp only [W]
  rw [wires_eq_foldl, foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]
lemma W_or (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (a b : ℕ) (hin : (gateAt C k).inputs = [a, b])
    (ha : a < n + k) (hb : b < n + k) :
    W n C x (n + k) = (W n C x a || W n C x b) := by
  rw [W_gate n C x k hk, hop, hin]
  simp [GateOp.eval, ha, hb]
lemma W_and (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.and) (a b : ℕ) (hin : (gateAt C k).inputs = [a, b])
    (ha : a < n + k) (hb : b < n + k) :
    W n C x (n + k) = (W n C x a && W n C x b) := by
  rw [W_gate n C x k hk, hop, hin]
  simp [GateOp.eval, ha, hb]
lemma appOr_gateAt_lt (n : ℕ) (C : Circuit) (a b k : ℕ) (hk : k < C.gates.length) :
    gateAt (appOr n C a b) k = gateAt C k := by
  simp [gateAt, appOr, List.getD_eq_getElem?_getD, List.getElem?_append_left hk]
lemma appOr_gateAt_last (n : ℕ) (C : Circuit) (a b : ℕ) :
    gateAt (appOr n C a b) C.gates.length = ⟨GateOp.or, [a, b]⟩ := by
  simp [gateAt, appOr, List.getD_eq_getElem?_getD]
lemma appOr_eval (n : ℕ) (C : Circuit) (a b : ℕ) (x : Fin n → Bool)
    (ha : a < n + C.gates.length) (hb : b < n + C.gates.length) :
    (appOr n C a b).eval (List.ofFn x) = (W n C x a || W n C x b) := by
  have h := W_or n (appOr n C a b) x C.gates.length (by simp [appOr]) (by rw [appOr_gateAt_last])
    a b (by rw [appOr_gateAt_last]) ha hb
  rw [appOr_W_lt n C a b x a ha, appOr_W_lt n C a b x b hb] at h
  exact h
def AO (n : ℕ) (C : Circuit) : Prop :=
  ∀ k < C.gates.length, ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) ∧
    ∃ a b, (gateAt C k).inputs = [a, b] ∧ a < n + k ∧ b < n + k
def Least (n : ℕ) (C : Circuit) : Prop :=
  AO n C ∧ ∀ D : Circuit, AO n D →
    (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) →
    C.gates.length ≤ D.gates.length
def Bel (n : ℕ) (C : Circuit) (j : ℕ) : Prop :=
  ∀ x : Fin n → Bool, W n C x (n + j) = true → C.eval (List.ofFn x) = true
lemma alias_lt (w i u N : ℕ) (hu : u < N + 1) (hi : i < w) (hw : w ≤ N) :
    aliasWire w i u < N := by
  unfold aliasWire shiftDown
  split_ifs <;> omega
lemma erase_AO (n : ℕ) (C : Circuit) (j i : ℕ) (hA : AO n C) (hj : j < C.gates.length)
    (hi : i < n + j) : AO n (eraseC n C j i) := by
  intro k hk
  have hlen := erase_length n C j i hj
  by_cases hkj : k < j
  · rw [erase_gateAt_lt n C j i k hj hkj]; exact hA k (by omega)
  · rw [erase_gateAt_ge n C j i k hj (by omega) (by omega)]
    obtain ⟨hop, a, b, hin, ha, hb⟩ := hA (k + 1) (by omega)
    refine ⟨hop, aliasWire (n + j) i a, aliasWire (n + j) i b, by simp [aliasGate, hin], ?_, ?_⟩
    · exact alias_lt (n + j) i a (n + k) (by omega) hi (by omega)
    · exact alias_lt (n + j) i b (n + k) (by omega) hi (by omega)
lemma appOr_AO (n : ℕ) (C : Circuit) (a b : ℕ) (hA : AO n C) (ha : a < n + C.gates.length)
    (hb : b < n + C.gates.length) : AO n (appOr n C a b) := by
  intro k hk
  have hlen : (appOr n C a b).gates.length = C.gates.length + 1 := by simp [appOr]
  by_cases hkl : k < C.gates.length
  · rw [appOr_gateAt_lt n C a b k hkl]; exact hA k hkl
  · have hke : k = C.gates.length := by omega
    subst hke
    rw [appOr_gateAt_last]
    exact ⟨Or.inr rfl, a, b, rfl, ha, hb⟩
lemma trunc_AO (n : ℕ) (C : Circuit) (m : ℕ) (hA : AO n C) (hm : m ≤ C.gates.length) :
    AO n (truncC C m) := by
  intro k hk
  have hk' : k < m := by simp [truncC] at hk; omega
  have h : gateAt (truncC C m) k = gateAt C k := by
    simp [gateAt, truncC, List.getD_eq_getElem?_getD, hk']
  rw [h]; exact hA k (by omega)
lemma trunc_W (n : ℕ) (C : Circuit) (m : ℕ) (x : Fin n → Bool) (u : ℕ) (hm : m ≤ C.gates.length)
    (hu : u < n + m) : W n (truncC C m) x u = W n C x u := by
  have h := prefix_W n (C.gates.take m) [] (C.gates.drop m) C.output C.output x u
    (by rw [List.length_take]; omega)
  have e1 : (⟨C.gates.take m ++ [], C.output⟩ : Circuit) = truncC C m := by simp [truncC]
  have e2 : (⟨C.gates.take m ++ C.gates.drop m, C.output⟩ : Circuit) = C := by
    cases C; simp
  rw [e1, e2] at h
  exact h
lemma least_out (n : ℕ) (C : Circuit) (hL : Least n C)
    (hT : ∃ x : Fin n → Bool, C.eval (List.ofFn x) = true)
    (hV : ∀ u : Fin n, ∃ x : Fin n → Bool, x u = true ∧ C.eval (List.ofFn x) = false) :
    n ≤ C.output ∧ C.output + 1 = n + C.gates.length := by
  have h1 : n ≤ C.output := by
    by_contra h
    push Not at h
    obtain ⟨x, hx, hf⟩ := hV ⟨C.output, h⟩
    have h2 : W n C x C.output = true := (W_input n C x C.output h).trans hx
    have h3 : W n C x C.output = false := hf
    rw [h2] at h3
    exact absurd h3 (by simp)
  have h2 : C.output < n + C.gates.length := by
    by_contra h
    obtain ⟨x, hx⟩ := hT
    have h3 : W n C x C.output = true := hx
    simp only [W] at h3
    rw [getD_ge_length _ _ (by rw [wires_length]; omega)] at h3
    exact absurd h3 (by simp)
  refine ⟨h1, ?_⟩
  by_contra h3
  have hm : C.output - n + 1 < C.gates.length := by omega
  have hfun : ∀ x : Fin n → Bool,
      (truncC C (C.output - n + 1)).eval (List.ofFn x) = C.eval (List.ofFn x) := fun x =>
    trunc_W n C (C.output - n + 1) x C.output (by omega) (by omega)
  have h4 := hL.2 _ (trunc_AO n C (C.output - n + 1) hL.1 (by omega)) hfun
  simp [truncC] at h4
  omega
lemma least_read (n : ℕ) (C : Circuit) (hL : Least n C)
    (hout : C.output + 1 = n + C.gates.length) (j : ℕ) (hj : j + 1 < C.gates.length) :
    ∃ k, j < k ∧ k < C.gates.length ∧ n + j ∈ (gateAt C k).inputs := by
  by_contra hno
  push Not at hno
  obtain ⟨hop, a, b, hin, ha, hb⟩ := hL.1 j (by omega)
  have hfun : ∀ x : Fin n → Bool,
      (eraseC n C j a).eval (List.ofFn x) = C.eval (List.ofFn x) := fun x =>
    erase_wires n C j a (by omega) ha x (Or.inr hno) C.output (by intro h; omega)
  have h1 := hL.2 _ (erase_AO n C j a hL.1 (by omega) ha) hfun
  have h2 := erase_length n C j a (by omega)
  omega
lemma least_nodup (n : ℕ) (C : Circuit) (hL : Least n C) (i j : ℕ) (hij : i < n + j)
    (hj : j < C.gates.length) : ∃ x : Fin n → Bool, W n C x i ≠ W n C x (n + j) := by
  by_contra hsame
  push Not at hsame
  have hfun : ∀ x : Fin n → Bool,
      (eraseC n C j i).eval (List.ofFn x) = C.eval (List.ofFn x) := fun x =>
    erase_wires n C j i hj hij x (Or.inl (hsame x)) C.output (fun _ => hsame x)
  have h1 := hL.2 _ (erase_AO n C j i hL.1 hj hij) hfun
  have h2 := erase_length n C j i hj
  omega
lemma red (n : ℕ) (C : Circuit) (hA : AO n C) (j r : ℕ) (hr : r < C.gates.length)
    (hmem : n + j ∈ (gateAt C r).inputs) :
    ∃ p, p < n + r ∧
      ∀ x : Fin n → Bool, W n C x (n + j) = false → W n C x p = W n C x (n + r) := by
  obtain ⟨hop, a, b, hin, ha, hb⟩ := hA r hr
  rw [hin] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hop with hop | hop
  · refine ⟨n + j, by rcases hmem with h | h <;> omega, fun x hx => ?_⟩
    rw [W_and n C x r hr hop a b hin ha hb, hx]
    rcases hmem with h | h
    · rw [← h, hx]; simp
    · rw [← h, hx]; simp
  · rcases hmem with h | h
    · refine ⟨b, hb, fun x hx => ?_⟩
      rw [W_or n C x r hr hop a b hin ha hb, ← h, hx]; simp
    · refine ⟨a, ha, fun x hx => ?_⟩
      rw [W_or n C x r hr hop a b hin ha hb, ← h, hx]; simp
lemma two_readers (n : ℕ) (C : Circuit) (hL : Least n C)
    (hout : C.output + 1 = n + C.gates.length) (j : ℕ) (hB : Bel n C j) (r1 r2 : ℕ)
    (h12 : r1 < r2) (hr2 : r2 < C.gates.length)
    (hm1 : n + j ∈ (gateAt C r1).inputs) (hm2 : n + j ∈ (gateAt C r2).inputs) : False := by
  have hA := hL.1
  have hj1 : j < r1 := by
    obtain ⟨_, a, b, hin, ha, hb⟩ := hA r1 (by omega)
    rw [hin] at hm1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm1
    omega
  obtain ⟨p2, hp2, hv2⟩ := red n C hA j r2 hr2 hm2
  have hA1 := erase_AO n C r2 p2 hA hr2 hp2
  have hl1 := erase_length n C r2 p2 hr2
  have hW1 : ∀ (x : Fin n → Bool) (u : ℕ), u < n + r2 →
      W n (eraseC n C r2 p2) x u = W n C x u := fun x u hu => erase_W_lt n C r2 p2 hr2 x u hu
  have hg1 : gateAt (eraseC n C r2 p2) r1 = gateAt C r1 := erase_gateAt_lt n C r2 p2 r1 hr2 h12
  obtain ⟨p1, hp1, hv1⟩ := red n (eraseC n C r2 p2) hA1 j r1 (by omega) (by rw [hg1]; exact hm1)
  have hA2 := erase_AO n (eraseC n C r2 p2) r1 p1 hA1 (by omega) hp1
  have hl2 := erase_length n (eraseC n C r2 p2) r1 p1 (by omega)
  have ho1 : (eraseC n C r2 p2).output < n + (eraseC n C r2 p2).gates.length :=
    alias_lt (n + r2) p2 C.output _ (by omega) hp2 (by omega)
  have ho2 : (eraseC n (eraseC n C r2 p2) r1 p1).output <
      n + (eraseC n (eraseC n C r2 p2) r1 p1).gates.length :=
    alias_lt (n + r1) p1 (eraseC n C r2 p2).output _ (by omega) hp1 (by omega)
  have hfun : ∀ x : Fin n → Bool,
      (appOr n (eraseC n (eraseC n C r2 p2) r1 p1)
        (eraseC n (eraseC n C r2 p2) r1 p1).output (n + j)).eval (List.ofFn x) =
        C.eval (List.ofFn x) := by
    intro x
    rw [appOr_eval n _ _ (n + j) x ho2 (by omega)]
    have hj2 : W n (eraseC n (eraseC n C r2 p2) r1 p1) x (n + j) = W n C x (n + j) := by
      rw [erase_W_lt n _ r1 p1 (by omega) x (n + j) (by omega), hW1 x (n + j) (by omega)]
    rw [hj2]
    cases hx : W n C x (n + j)
    · have e2 := erase_wires n C r2 p2 hr2 hp2 x (Or.inl (hv2 x hx)) C.output (fun _ => hv2 x hx)
      have hx1 : W n (eraseC n C r2 p2) x (n + j) = false := by
        rw [hW1 x _ (by omega)]; exact hx
      have e1 := erase_wires n (eraseC n C r2 p2) r1 p1 (by omega) hp1 x (Or.inl (hv1 x hx1))
        (eraseC n C r2 p2).output (fun _ => hv1 x hx1)
      rw [Bool.or_false]
      exact e1.trans e2
    · rw [Bool.or_true]; exact (hB x hx).symm
  have h1 := hL.2 _ (appOr_AO n _ _ (n + j) hA2 ho2 (by omega)) hfun
  have h2 : (appOr n (eraseC n (eraseC n C r2 p2) r1 p1)
      (eraseC n (eraseC n C r2 p2) r1 p1).output (n + j)).gates.length =
      (eraseC n (eraseC n C r2 p2) r1 p1).gates.length + 1 := by simp [appOr]
  omega
lemma one_reader (n : ℕ) (C : Circuit) (hL : Least n C)
    (hout : C.output + 1 = n + C.gates.length) (j : ℕ) (hj : j < C.gates.length)
    (hB : Bel n C j) (hne : n + j ≠ C.output) :
    ∃ r, r < C.gates.length ∧ n + j ∈ (gateAt C r).inputs ∧
      (∀ k, k < C.gates.length → n + j ∈ (gateAt C k).inputs → k = r) ∧
      (gateAt C r).op = GateOp.or := by
  have hA := hL.1
  obtain ⟨r, hjr, hr, hmr⟩ := least_read n C hL hout j (by omega)
  have huniq : ∀ k, k < C.gates.length → n + j ∈ (gateAt C k).inputs → k = r := by
    intro k hk hmk
    by_contra hkr
    rcases Nat.lt_or_gt_of_ne hkr with h | h
    · exact two_readers n C hL hout j hB k r h hr hmk hmr
    · exact two_readers n C hL hout j hB r k h hk hmr hmk
  refine ⟨r, hr, hmr, huniq, ?_⟩
  obtain ⟨hop, a, b, hin, ha, hb⟩ := hA r hr
  rcases hop with hop | hop
  swap
  · exact hop
  exfalso
  have hle : ∀ x : Fin n → Bool, W n C x (n + r) = true → W n C x (n + j) = true := by
    intro x hx
    rw [W_and n C x r hr hop a b hin ha hb] at hx
    have hmr' := hmr
    rw [hin] at hmr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmr'
    rcases hmr' with h | h
    · rw [h]; simp_all
    · rw [h]; simp_all
  by_cases hro : n + r = C.output
  · obtain ⟨x, hx⟩ := least_nodup n C hL (n + j) r (by omega) hr
    apply hx
    cases h1 : W n C x (n + r)
    · cases h2 : W n C x (n + j)
      · rfl
      · have h3 : W n C x C.output = true := hB x h2
        rw [← hro, h1] at h3
        exact absurd h3 (by simp)
    · exact hle x h1
  · obtain ⟨s, hrs, hs, hms⟩ := least_read n C hL hout r (by omega)
    have hv : ∀ x : Fin n → Bool, W n C x (n + j) = false →
        W n C x (n + j) = W n C x (n + r) := by
      intro x hx
      cases h1 : W n C x (n + r)
      · exact hx
      · rw [hle x h1] at hx; exact absurd hx (by simp)
    have hA1 := erase_AO n C r (n + j) hA hr (by omega)
    have hl1 := erase_length n C r (n + j) hr
    have ho1 : (eraseC n C r (n + j)).output < n + (eraseC n C r (n + j)).gates.length :=
      alias_lt (n + r) (n + j) C.output _ (by omega) (by omega) (by omega)
    have hWj : ∀ x : Fin n → Bool, W n (eraseC n C r (n + j)) x (n + j) = W n C x (n + j) :=
      fun x => erase_W_lt n C r (n + j) hr x (n + j) (by omega)
    have hfun : ∀ x : Fin n → Bool,
        (appOr n (eraseC n C r (n + j)) (eraseC n C r (n + j)).output (n + j)).eval (List.ofFn x) =
          C.eval (List.ofFn x) := by
      intro x
      rw [appOr_eval n _ _ (n + j) x ho1 (by omega), hWj x]
      cases hx : W n C x (n + j)
      · rw [Bool.or_false]
        exact erase_wires n C r (n + j) hr (by omega) x (Or.inl (hv x hx)) C.output
          (fun _ => hv x hx)
      · rw [Bool.or_true]; exact (hB x hx).symm
    have hA3 := appOr_AO n _ _ (n + j) hA1 ho1 (by omega)
    have hl3 : (appOr n (eraseC n C r (n + j)) (eraseC n C r (n + j)).output (n + j)).gates.length =
        C.gates.length := by simp [appOr]; omega
    have hL3 : Least n (appOr n (eraseC n C r (n + j)) (eraseC n C r (n + j)).output (n + j)) :=
      ⟨hA3, fun D hD hDf => by
        rw [hl3]; exact hL.2 D hD (fun x => (hDf x).trans (hfun x))⟩
    have hB3 : Bel n (appOr n (eraseC n C r (n + j)) (eraseC n C r (n + j)).output (n + j)) j := by
      intro x hx
      rw [hfun x]
      apply hB x
      rw [appOr_W_lt n _ _ _ x (n + j) (by omega), hWj x] at hx
      exact hx
    refine two_readers n _ hL3 (by simp [appOr]; omega) j hB3 (s - 1) (C.gates.length - 1)
      (by omega) (by rw [hl3]; omega) ?_ ?_
    · rw [appOr_gateAt_lt n _ _ _ (s - 1) (by omega),
        erase_gateAt_ge n C r (n + j) (s - 1) hr (by omega) (by omega)]
      have hs1 : s - 1 + 1 = s := by omega
      rw [hs1]
      simp only [aliasGate, List.mem_map]
      exact ⟨n + r, hms, by simp [aliasWire]⟩
    · have hs2 : C.gates.length - 1 = (eraseC n C r (n + j)).gates.length := by omega
      rw [hs2, appOr_gateAt_last]
      simp
lemma or_children (n : ℕ) (C : Circuit) (hL : Least n C)
    (hV : ∀ u : Fin n, ∃ x : Fin n → Bool, x u = true ∧ C.eval (List.ofFn x) = false)
    (r : ℕ) (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) (hB : Bel n C r) :
    ∃ a b, (gateAt C r).inputs = [n + a, n + b] ∧ a < r ∧ b < r ∧ a ≠ b ∧
      Bel n C a ∧ Bel n C b := by
  obtain ⟨_, a, b, hin, ha, hb⟩ := hL.1 r hr
  have hWr := fun x => W_or n C x r hr hop a b hin ha hb
  have hvar : ∀ c, c < n → (∀ x : Fin n → Bool, W n C x c = true → W n C x (n + r) = true) →
      False := by
    intro c hc hcr
    obtain ⟨x, hx, hf⟩ := hV ⟨c, hc⟩
    have h1 : W n C x c = true := (W_input n C x c hc).trans hx
    have h2 := hB x (hcr x h1)
    rw [hf] at h2
    exact absurd h2 (by simp)
  have hna : n ≤ a := by
    by_contra h
    push Not at h
    exact hvar a h (fun x hx => by rw [hWr x, hx]; rfl)
  have hnb : n ≤ b := by
    by_contra h
    push Not at h
    exact hvar b h (fun x hx => by rw [hWr x, hx]; simp)
  obtain ⟨a', rfl⟩ := Nat.exists_eq_add_of_le hna
  obtain ⟨b', rfl⟩ := Nat.exists_eq_add_of_le hnb
  refine ⟨a', b', hin, by omega, by omega, ?_, ?_, ?_⟩
  · intro hab
    subst hab
    obtain ⟨x, hx⟩ := least_nodup n C hL (n + a') r ha hr
    exact hx (by rw [hWr x]; simp)
  · intro x hx; exact hB x (by rw [hWr x, hx]; rfl)
  · intro x hx; exact hB x (by rw [hWr x, hx]; simp)
lemma has_top (n : ℕ) (C : Circuit) (hL : Least n C)
    (hV : ∀ u : Fin n, ∃ x : Fin n → Bool, x u = true ∧ C.eval (List.ofFn x) = false)
    (Cone : ℕ → ℕ → Prop)
    (c1 : ∀ i k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → Cone i k)
    (c2 : ∀ t i k, k < C.gates.length → Cone t i → n + i ∈ (gateAt C k).inputs → Cone t k) :
    ∀ j, j < C.gates.length → Bel n C j →
      ∃ t, t < C.gates.length ∧ (gateAt C t).op = GateOp.and ∧ Bel n C t ∧ (t = j ∨ Cone t j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj hB
    rcases (hL.1 j hj).1 with hop | hop
    · exact ⟨j, hj, hop, hB, Or.inl rfl⟩
    · obtain ⟨a, b, hin, ha, hb, hab, hBa, hBb⟩ := or_children n C hL hV j hj hop hB
      obtain ⟨t, ht, hopt, hBt, htj⟩ := ih a ha (by omega) hBa
      refine ⟨t, ht, hopt, hBt, Or.inr ?_⟩
      have hmem : n + a ∈ (gateAt C j).inputs := by rw [hin]; simp
      rcases htj with rfl | h
      · exact c1 _ j hj hmem
      · exact c2 t a j hj h hmem
lemma up (n : ℕ) (C : Circuit) (hL : Least n C) (hout : C.output + 1 = n + C.gates.length)
    (Cone : ℕ → ℕ → Prop)
    (c2 : ∀ t i k, k < C.gates.length → Cone t i → n + i ∈ (gateAt C k).inputs → Cone t k)
    (t : ℕ) (hTop : ∀ s, s < C.gates.length → (gateAt C s).op = GateOp.and → ¬ Cone t s) :
    ∀ d s, s < C.gates.length → C.gates.length - s = d → Cone t s → Bel n C s := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro s hs hd hc
    by_cases hso : n + s = C.output
    · intro x hx
      have h1 : W n C x C.output = true := by rw [← hso]; exact hx
      exact h1
    · obtain ⟨k, hsk, hk, hmk⟩ := least_read n C hL hout s (by omega)
      have hck := c2 t s k hk hc hmk
      have hBk := ih (C.gates.length - k) (by omega) k hk rfl hck
      obtain ⟨hop, a, b, hin, ha, hb⟩ := hL.1 k hk
      have hopk : (gateAt C k).op = GateOp.or := by
        rcases hop with h | h
        · exact absurd hck (hTop k hk h)
        · exact h
      intro x hx
      apply hBk x
      rw [W_or n C x k hk hopk a b hin ha hb]
      rw [hin] at hmk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmk
      rcases hmk with h | h
      · rw [← h, hx]; rfl
      · rw [← h, hx]; simp
theorem main_abs (n : ℕ) (C : Circuit) (hL : Least n C)
    (hT : ∃ x : Fin n → Bool, C.eval (List.ofFn x) = true)
    (hV : ∀ u : Fin n, ∃ x : Fin n → Bool, x u = true ∧ C.eval (List.ofFn x) = false)
    (Cone : ℕ → ℕ → Prop)
    (c1 : ∀ i k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → Cone i k)
    (c2 : ∀ t i k, k < C.gates.length → Cone t i → n + i ∈ (gateAt C k).inputs → Cone t k)
    (hTop : ∀ t s, t < C.gates.length → s < C.gates.length → (gateAt C t).op = GateOp.and →
      Bel n C t → (gateAt C s).op = GateOp.and → ¬ Cone t s) :
    (∀ j, j < C.gates.length → Bel n C j → n + j ≠ C.output →
      ∃ r, r < C.gates.length ∧ n + j ∈ (gateAt C r).inputs ∧
        (∀ k, k < C.gates.length → n + j ∈ (gateAt C k).inputs → k = r) ∧
        (gateAt C r).op = GateOp.or ∧ Bel n C r) ∧
    (n ≤ C.output ∧ C.output + 1 = n + C.gates.length) ∧
    (∀ O A : Finset ℕ,
      (∀ k, k ∈ O ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧ Bel n C k) →
      (∀ k, k ∈ A ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧ Bel n C k) →
      O.card + 1 = A.card) := by
  have hout := least_out n C hL hT hV
  have part1 : ∀ j, j < C.gates.length → Bel n C j → n + j ≠ C.output →
      ∃ r, r < C.gates.length ∧ n + j ∈ (gateAt C r).inputs ∧
        (∀ k, k < C.gates.length → n + j ∈ (gateAt C k).inputs → k = r) ∧
        (gateAt C r).op = GateOp.or ∧ Bel n C r := by
    intro j hj hB hne
    obtain ⟨r, hr, hmr, huniq, hopr⟩ := one_reader n C hL hout.2 j hj hB hne
    refine ⟨r, hr, hmr, huniq, hopr, ?_⟩
    obtain ⟨t, ht, hopt, hBt, htj⟩ := has_top n C hL hV Cone c1 c2 j hj hB
    have hc : Cone t r := by
      rcases htj with rfl | h
      · exact c1 _ r hr hmr
      · exact c2 t j r hr h hmr
    exact up n C hL hout.2 Cone c2 t (fun s hs hops => hTop t s ht hs hopt hBt hops) _ r hr rfl hc
  refine ⟨part1, hout, ?_⟩
  intro O A hO hA
  classical
  have hBo : Bel n C (C.gates.length - 1) := by
    intro x hx
    have h1 : n + (C.gates.length - 1) = C.output := by omega
    rw [h1] at hx
    exact hx
  have hoB : C.gates.length - 1 ∈ O ∪ A := by
    rcases (hL.1 (C.gates.length - 1) (by omega)).1 with h | h
    · exact Finset.mem_union_right _ ((hA _).2 ⟨by omega, h, hBo⟩)
    · exact Finset.mem_union_left _ ((hO _).2 ⟨by omega, h, hBo⟩)
  have hdisj : Disjoint O A := by
    rw [Finset.disjoint_left]
    intro k h1 h2
    have e1 := ((hO k).1 h1).2.1
    have e2 := ((hA k).1 h2).2.1
    rw [e1] at e2
    cases e2
  obtain ⟨B, hBdef⟩ : ∃ B, B = (O ∪ A).erase (C.gates.length - 1) := ⟨_, rfl⟩
  have hBmem : ∀ j, j ∈ B ↔ j < C.gates.length ∧ Bel n C j ∧ n + j ≠ C.output := by
    intro j
    rw [hBdef, Finset.mem_erase, Finset.mem_union, hO, hA]
    constructor
    · rintro ⟨h1, h2 | h2⟩
      · exact ⟨h2.1, h2.2.2, by omega⟩
      · exact ⟨h2.1, h2.2.2, by omega⟩
    · rintro ⟨h1, h2, h3⟩
      refine ⟨by omega, ?_⟩
      rcases (hL.1 j h1).1 with h | h
      · exact Or.inr ⟨h1, h, h2⟩
      · exact Or.inl ⟨h1, h, h2⟩
  have hcount := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := B) (t := O)
    (fun j k => n + j ∈ (gateAt C k).inputs)
  have hleft : ∀ j ∈ B,
      (Finset.bipartiteAbove (fun j k => n + j ∈ (gateAt C k).inputs) O j).card = 1 := by
    intro j hj
    obtain ⟨hj1, hj2, hj3⟩ := (hBmem j).1 hj
    obtain ⟨r, hr, hmr, huniq, hopr, hBr⟩ := part1 j hj1 hj2 hj3
    rw [Finset.card_eq_one]
    refine ⟨r, ?_⟩
    ext k
    simp only [Finset.bipartiteAbove, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hk, hmk⟩
      exact huniq k ((hO k).1 hk).1 hmk
    · rintro rfl
      exact ⟨(hO _).2 ⟨hr, hopr, hBr⟩, hmr⟩
  have hright : ∀ k ∈ O,
      (Finset.bipartiteBelow (fun j k => n + j ∈ (gateAt C k).inputs) B k).card = 2 := by
    intro k hk
    obtain ⟨hk1, hk2, hk3⟩ := (hO k).1 hk
    obtain ⟨a, b, hin, ha, hb, hab, hBa, hBb⟩ := or_children n C hL hV k hk1 hk2 hk3
    rw [Finset.card_eq_two]
    refine ⟨a, b, hab, ?_⟩
    ext j
    simp only [Finset.bipartiteBelow, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
      hin, List.mem_cons, List.not_mem_nil, or_false, hBmem]
    constructor
    · rintro ⟨_, h | h⟩
      · left; omega
      · right; omega
    · rintro (rfl | rfl)
      · exact ⟨⟨by omega, hBa, by omega⟩, Or.inl rfl⟩
      · exact ⟨⟨by omega, hBb, by omega⟩, Or.inr rfl⟩
  rw [Finset.sum_congr rfl hleft, Finset.sum_congr rfl hright] at hcount
  simp only [Finset.sum_const, smul_eq_mul] at hcount
  have hBc : B.card = (O ∪ A).card - 1 := by rw [hBdef]; exact Finset.card_erase_of_mem hoB
  have hU : (O ∪ A).card = O.card + A.card := Finset.card_union_of_disjoint hdisj
  have hpos : 0 < (O ∪ A).card := Finset.card_pos.mpr ⟨_, hoB⟩
  omega
lemma coneFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega
lemma coneStep_getD_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    (coneStep n cs g).getD cs.length [] =
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) []) := by
  simp [coneStep, List.getD_eq_getElem?_getD]
lemma coneStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (coneStep n cs g).getD m [] = cs.getD m [] := by
  simp [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]
lemma coneFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (coneStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (coneStep n cs g) (by simp [coneStep]; omega)]
    exact coneStep_getD_lt n cs g k hk
lemma inCone_iff (n : ℕ) (C : Circuit) (i k : ℕ) (hk : k < C.gates.length) :
    InCone n C i k ↔ ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
      (i = w - n ∨ InCone n C i (w - n)) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : cones n C = post.foldl (coneStep n) (coneStep n (pre.foldl (coneStep n) []) gk) := by
    simp only [cones]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (coneStep n) []).length = k := by
    rw [coneFold_length]; simp [hpre_len]
  have hl1 : (coneStep n (pre.foldl (coneStep n) []) gk).length = k + 1 := by
    simp [coneStep, hl0]
  have h1 : (cones n C).getD k [] =
      (gk.inputs.filter (fun w => decide (n ≤ w ∧ w < n + k))).flatMap
        (fun w => (w - n) :: (pre.foldl (coneStep n) []).getD (w - n) []) := by
    rw [hc, coneFold_getD_lt n post _ k (by omega)]
    have h := coneStep_getD_last n (pre.foldl (coneStep n) []) gk
    rw [hl0] at h
    exact h
  have h2 : ∀ m, m < k → (cones n C).getD m [] = (pre.foldl (coneStep n) []).getD m [] := by
    intro m hm
    rw [hc, coneFold_getD_lt n post _ m (by omega)]
    exact coneStep_getD_lt n _ gk m (by omega)
  unfold InCone
  rw [h1]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw, hn, hlt⟩, h⟩
    refine ⟨w, hw, hn, hlt, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [h2 (w - n) (by omega)]
      exact h
  · rintro ⟨w, hw, hn, hlt, h⟩
    refine ⟨w, ⟨hw, hn, hlt⟩, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [← h2 (w - n) (by omega)]
      exact h
lemma inCone_c1 (n : ℕ) (C : Circuit) (hA : AO n C) (i k : ℕ) (hk : k < C.gates.length)
    (hm : n + i ∈ (gateAt C k).inputs) : InCone n C i k := by
  rw [inCone_iff n C i k hk]
  have hlt : n + i < n + k := by
    obtain ⟨_, a, b, hin, ha, hb⟩ := hA k hk
    rw [hin] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    omega
  exact ⟨n + i, hm, by omega, hlt, Or.inl (by omega)⟩
lemma inCone_c2 (n : ℕ) (C : Circuit) (hA : AO n C) (t i k : ℕ) (hk : k < C.gates.length)
    (hc : InCone n C t i) (hm : n + i ∈ (gateAt C k).inputs) : InCone n C t k := by
  rw [inCone_iff n C t k hk]
  have hlt : n + i < n + k := by
    obtain ⟨_, a, b, hin, ha, hb⟩ := hA k hk
    rw [hin] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    omega
  have he : n + i - n = i := by omega
  exact ⟨n + i, hm, by omega, hlt, Or.inr (by rw [he]; exact hc)⟩
lemma edge_true (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : G.edgeFinset.Nonempty) :
    ∃ x : Fin n → Bool, ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
  obtain ⟨e, he⟩ := h
  induction e using Sym2.ind with
  | _ u v =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    exact ⟨fun _ => true, u, v, he, rfl, rfl⟩
lemma edge_var (n : ℕ) (G : SimpleGraph (Fin n)) (u : Fin n) :
    ∃ x : Fin n → Bool, x u = true ∧ ¬ ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true := by
  refine ⟨fun w => decide (w = u), by simp, ?_⟩
  rintro ⟨a, b, hab, ha, hb⟩
  simp only [decide_eq_true_eq] at ha hb
  subst ha
  subst hb
  exact G.loopless.irrefl _ hab
lemma gf_true (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : G.edgeFinset.Nonempty) : ∃ x : Fin n → Bool, graphFun G ∅ x = true := by
  obtain ⟨x, hx⟩ := edge_true n G h
  exact ⟨x, by simp only [graphFun, Bool.or_eq_true, decide_eq_true_eq]; exact Or.inr hx⟩
lemma gf_var (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u : Fin n) :
    ∃ x : Fin n → Bool, x u = true ∧ graphFun G ∅ x = false := by
  obtain ⟨x, hx, hno⟩ := edge_var n G u
  refine ⟨x, hx, ?_⟩
  simp only [graphFun, Bool.or_eq_false_iff, decide_eq_false_iff_not]
  exact ⟨by simp, hno⟩
lemma AO_of_IsAO2 (n : ℕ) (C : Circuit) (h : PEqualNP.TopForm.IsAO2 n C) : AO n C := by
  obtain ⟨hao, hrb, hlen⟩ := h
  intro k hk
  have hmem : gateAt C k ∈ C.gates := by
    rw [gateAt_eq C k hk]; exact List.getElem_mem hk
  have hl := hlen _ hmem
  refine ⟨hao _ hmem, ?_⟩
  match hin : (gateAt C k).inputs, hl with
  | [a, b], _ =>
    exact ⟨a, b, rfl, hrb k hk a (by rw [hin]; simp), hrb k hk b (by rw [hin]; simp)⟩
lemma IsAO2_of_AO (n : ℕ) (C : Circuit) (h : AO n C) : PEqualNP.TopForm.IsAO2 n C := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hg
    rw [← gateAt_eq C k hk]
    exact (h k hk).1
  · intro k hk i hi
    obtain ⟨_, a, b, hin, ha, hb⟩ := h k hk
    rw [hin] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact ha
    · exact hb
  · intro g hg
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hg
    rw [← gateAt_eq C k hk]
    obtain ⟨_, a, b, hin, _, _⟩ := h k hk
    rw [hin]; rfl
theorem main_real (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hne : G.edgeFinset.Nonempty) (hL : PEqualNP.TopForm.IsLeastAO G C)
    (hTF : PEqualNP.TopForm.TopForm G C) :
    (∀ j < C.gates.length, PEqualNP.TopForm.BelowF G C j → n + j ≠ C.output →
      ∃ r, PEqualNP.TopForm.readers n C j = {r} ∧ (gateAt C r).op = GateOp.or ∧
        PEqualNP.TopForm.BelowF G C r) ∧
    PEqualNP.TopForm.readers n C (C.output - n) = ∅ ∧
    (PEqualNP.TopForm.orT G C).card + 1 = (PEqualNP.TopForm.tops G C).card := by
  have hfun : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = graphFun G ∅ x := fun x =>
    congrFun hL.2.1 x
  have hAO : AO n C := AO_of_IsAO2 n C hL.1
  have hLeast : Least n C := ⟨hAO, fun D hD hDf =>
    hL.2.2 D (IsAO2_of_AO n D hD) (funext fun x => (hDf x).trans (hfun x))⟩
  have hT : ∃ x : Fin n → Bool, C.eval (List.ofFn x) = true := by
    obtain ⟨x, hx⟩ := gf_true n G hne
    exact ⟨x, (hfun x).trans hx⟩
  have hV : ∀ u : Fin n, ∃ x : Fin n → Bool, x u = true ∧ C.eval (List.ofFn x) = false := by
    intro u
    obtain ⟨x, hx, hf⟩ := gf_var n G u
    exact ⟨x, hx, (hfun x).trans hf⟩
  have hBel : ∀ j, PEqualNP.TopForm.BelowF G C j ↔ Bel n C j := fun j =>
    ⟨fun h x hx => (hfun x).trans (h x hx), fun h x hx => (hfun x).symm.trans (h x hx)⟩
  obtain ⟨p1, p2, p3⟩ := main_abs n C hLeast hT hV (InCone n C) (inCone_c1 n C hAO)
    (inCone_c2 n C hAO)
    (fun t s ht hs hopt hBt hops => hTF t ht s hs hopt ((hBel t).2 hBt) hops)
  refine ⟨?_, ?_, ?_⟩
  · intro j hj hB hne'
    obtain ⟨r, hr, hmr, huniq, hopr, hBr⟩ := p1 j hj ((hBel j).1 hB) hne'
    refine ⟨r, ?_, hopr, (hBel r).2 hBr⟩
    ext k
    simp only [PEqualNP.TopForm.readers, Finset.mem_filter, Finset.mem_range,
      Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩
      exact huniq k h1 h2
    · rintro rfl
      exact ⟨hr, hmr⟩
  · rw [Finset.eq_empty_iff_forall_notMem]
    intro k hk
    simp only [PEqualNP.TopForm.readers, Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨_, a, b, hin, ha, hb⟩ := hAO k hk.1
    have h2 := hk.2
    rw [hin] at h2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
    omega
  · refine p3 _ _ (fun k => ?_) (fun k => ?_)
    · simp only [PEqualNP.TopForm.orT, PEqualNP.TopForm.gatesWhere, Finset.mem_filter,
        Finset.mem_range, hBel]
    · simp only [PEqualNP.TopForm.tops, PEqualNP.TopForm.gatesWhere, Finset.mem_filter,
        Finset.mem_range, hBel]
end S98
theorem cover_g {α : Type} [DecidableEq α] (n : ℕ) (g : ℕ → Gate)
    (hback : ∀ k, ∀ i ∈ (g k).inputs, i < n + k)
    (f : ℕ → Finset α)
    (hf : ∀ k, (g k).op = GateOp.or →
      ∀ u, u ∈ f (n + k) ↔ ∃ w ∈ (g k).inputs, u ∈ f w)
    (Z : Finset ℕ) (r : ℕ) (R : Finset ℕ)
    (hR : ∀ k, k ∈ R ↔ Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
      (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k)
    (stops : Finset ℕ)
    (hstops : ∀ w, w ∈ stops ↔
      (w < n ∧ ∃ k ∈ R, k ∉ Z ∧ (g k).op = GateOp.or ∧ w ∈ (g k).inputs) ∨
      (n ≤ w ∧ w - n ∈ R ∧ (w - n ∈ Z ∨ (g (w - n)).op ≠ GateOp.or))) :
    f (n + r) ⊆ stops.biUnion f ∧ ∀ k, k ∈ R → f (n + k) ⊆ f (n + r) := by
  have hdown : ∀ k, k ∈ R → f (n + k) ⊆ stops.biUnion f := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk u hu
      by_cases hs : k ∈ Z ∨ (g k).op ≠ GateOp.or
      · refine Finset.mem_biUnion.2 ⟨n + k, (hstops _).2 (Or.inr ⟨by omega, ?_, ?_⟩), hu⟩
        · rwa [Nat.add_sub_cancel_left]
        · rwa [Nat.add_sub_cancel_left]
      · have hkZ : k ∉ Z := fun h => hs (Or.inl h)
        have hor : (g k).op = GateOp.or := by
          by_contra h
          exact hs (Or.inr h)
        obtain ⟨w, hw, huw⟩ := (hf k hor u).1 hu
        by_cases hwn : w < n
        · exact Finset.mem_biUnion.2 ⟨w, (hstops _).2 (Or.inl ⟨hwn, k, hk, hkZ, hor, hw⟩), huw⟩
        · have hwk := hback k w hw
          have hweq : n + (w - n) = w := by omega
          have hwR : w - n ∈ R :=
            (hR _).2 (((hR k).1 hk).tail ⟨hkZ, hor, by rwa [hweq]⟩)
          exact ih (w - n) (by omega) hwR (by rwa [hweq])
  have hup : ∀ k, k ∈ R → f (n + k) ⊆ f (n + r) := by
    intro k hk
    have h := (hR k).1 hk
    clear hk
    induction h with
    | refl => exact Finset.Subset.refl _
    | tail _ hbc ih =>
      intro u hu
      exact ih ((hf _ hbc.2.1 u).2 ⟨_, hbc.2.2, hu⟩)
  exact ⟨hdown r ((hR r).2 Relation.ReflTransGen.refl), hup⟩
theorem cover_bound (n : ℕ) (H : SimpleGraph (Fin n)) (T : Finset ℕ) (c : ℕ → Fin n)
    (hcov : ∀ u v : Fin n, H.Adj u v → ∃ a, a ∈ T ∧ (c a = u ∨ c a = v))
    (K : Finset (Fin n)) (hK : IsMinCover H K) : K.card ≤ T.card := by
  classical
  refine (hK.2 (T.image c) ?_).trans Finset.card_image_le
  intro u v huv
  obtain ⟨a, ha, h | h⟩ := hcov u v huv
  · left
    rw [Finset.mem_coe, ← h]
    exact Finset.mem_image_of_mem _ ha
  · right
    rw [Finset.mem_coe, ← h]
    exact Finset.mem_image_of_mem _ ha
theorem four_split (N : ℕ) (isAnd isOr bel : ℕ → Prop)
    (hAO : ∀ k, k < N → (isAnd k ∧ ¬ isOr k) ∨ (isOr k ∧ ¬ isAnd k))
    (T J O Q : Finset ℕ)
    (hT : ∀ k, k ∈ T ↔ k < N ∧ isAnd k ∧ bel k)
    (hJ : ∀ k, k ∈ J ↔ k < N ∧ isAnd k ∧ ¬ bel k)
    (hO : ∀ k, k ∈ O ↔ k < N ∧ isOr k ∧ bel k)
    (hQ : ∀ k, k ∈ Q ↔ k < N ∧ isOr k ∧ ¬ bel k) :
    T.card + J.card + O.card + Q.card = N := by
  classical
  have h1 : Disjoint T J := by
    rw [Finset.disjoint_left]
    intro k h h'
    exact ((hJ k).1 h').2.2 ((hT k).1 h).2.2
  have h2 : Disjoint (T ∪ J) O := by
    rw [Finset.disjoint_left]
    intro k h h'
    have ho := (hO k).1 h'
    rcases hAO k ho.1 with ha | ha
    · exact ha.2 ho.2.1
    · rcases Finset.mem_union.1 h with h | h
      · exact ha.2 ((hT k).1 h).2.1
      · exact ha.2 ((hJ k).1 h).2.1
  have h3 : Disjoint (T ∪ J ∪ O) Q := by
    rw [Finset.disjoint_left]
    intro k h h'
    have hq := (hQ k).1 h'
    rcases Finset.mem_union.1 h with h | h
    · rcases hAO k hq.1 with ha | ha
      · exact ha.2 hq.2.1
      · rcases Finset.mem_union.1 h with h | h
        · exact ha.2 ((hT k).1 h).2.1
        · exact ha.2 ((hJ k).1 h).2.1
    · exact hq.2.2 ((hO k).1 h).2.2
  have h4 : T ∪ J ∪ O ∪ Q = Finset.range N := by
    ext k
    simp only [Finset.mem_union, Finset.mem_range, hT, hJ, hO, hQ]
    constructor
    · rintro (((h | h) | h) | h) <;> exact h.1
    · intro hk
      by_cases hb : bel k
      · rcases hAO k hk with ha | ha
        · exact Or.inl (Or.inl (Or.inl ⟨hk, ha.1, hb⟩))
        · exact Or.inl (Or.inr ⟨hk, ha.1, hb⟩)
      · rcases hAO k hk with ha | ha
        · exact Or.inl (Or.inl (Or.inr ⟨hk, ha.1, hb⟩))
        · exact Or.inr ⟨hk, ha.1, hb⟩
  have h5 := congrArg Finset.card h4
  rw [Finset.card_union_of_disjoint h3, Finset.card_union_of_disjoint h2,
    Finset.card_union_of_disjoint h1, Finset.card_range] at h5
  exact h5
def TwoNe {α : Type} (g : ℕ → Gate) (f : ℕ → Finset α) (k : ℕ) : Prop :=
  ∃ w1 ∈ (g k).inputs, ∃ w2 ∈ (g k).inputs, w1 ≠ w2 ∧ (f w1).Nonempty ∧ (f w2).Nonempty
theorem cone_count2 {α : Type} [DecidableEq α] (n : ℕ) (g : ℕ → Gate) (f : ℕ → Finset α)
    (hf2 : ∀ k, (g k).op = GateOp.or →
      ∀ u, u ∈ f (n + k) ↔ ∃ w ∈ (g k).inputs, u ∈ f w)
    (Z : Finset ℕ)
    (hlen : ∀ k, k ∉ Z → (g k).op = GateOp.or → (g k).inputs.length ≤ 2)
    (r : ℕ) (R : Finset ℕ)
    (hR : ∀ k, k ∈ R ↔ Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
      (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k)
    (stops : Finset ℕ)
    (hstops : ∀ w, w ∈ stops ↔
      (w < n ∧ ∃ k ∈ R, k ∉ Z ∧ (g k).op = GateOp.or ∧ w ∈ (g k).inputs) ∨
      (n ≤ w ∧ w - n ∈ R ∧ (w - n ∈ Z ∨ (g (w - n)).op ≠ GateOp.or)))
    (I : Finset ℕ)
    (hI : ∀ k, k ∈ R → k ∉ Z → (g k).op = GateOp.or → TwoNe g f k → k ∈ I) :
    (stops.filter (fun w => (f w).Nonempty)).card ≤ I.card + 1 := by
  classical
  set E : Finset ℕ := R.filter (fun k => k ∉ Z ∧ (g k).op = GateOp.or) with hE
  set N : ℕ → Finset ℕ := fun k => (g k).inputs.toFinset.filter (fun w => (f w).Nonempty)
    with hN
  set U : Finset ℕ := insert (n + r) (E.biUnion N) with hU
  set E2 := E.filter (fun k => 2 ≤ (N k).card) with hE2
  set Ene := E.filter (fun k => (f (n + k)).Nonempty) with hEne
  have hE2I : E2 ⊆ I := by
    intro k hk
    simp only [hE2, hE, Finset.mem_filter] at hk
    obtain ⟨⟨hkR, hkZ, hor⟩, h2⟩ := hk
    apply hI k hkR hkZ hor
    obtain ⟨w1, hw1, w2, hw2, hne⟩ := Finset.one_lt_card.1 (by omega : 1 < (N k).card)
    simp only [hN, Finset.mem_filter, List.mem_toFinset] at hw1 hw2
    exact ⟨w1, hw1.1, w2, hw2.1, hne, hw1.2, hw2.2⟩
  have hNk : ∀ k ∈ E, (N k).card ≤ (if 2 ≤ (N k).card then 1 else 0) +
      (if (f (n + k)).Nonempty then 1 else 0) := by
    intro k hk
    simp only [hE, Finset.mem_filter] at hk
    have hc : (N k).card ≤ 2 := (Finset.card_filter_le _ _).trans
      ((List.toFinset_card_le _).trans (hlen k hk.2.1 hk.2.2))
    have hne : 1 ≤ (N k).card → (f (n + k)).Nonempty := by
      intro h1
      obtain ⟨w, hw⟩ := Finset.card_pos.1 (by omega : 0 < (N k).card)
      simp only [hN, Finset.mem_filter, List.mem_toFinset] at hw
      obtain ⟨u, hu⟩ := hw.2
      exact ⟨u, (hf2 k hk.2.2 u).2 ⟨w, hw.1, hu⟩⟩
    rcases Nat.lt_or_ge (N k).card 1 with h0 | h0
    · omega
    · rw [if_pos (hne h0)]
      split_ifs <;> omega
  have hsum : (E.biUnion N).card ≤ E2.card + Ene.card := by
    calc (E.biUnion N).card ≤ ∑ k ∈ E, (N k).card := Finset.card_biUnion_le
      _ ≤ ∑ k ∈ E, ((if 2 ≤ (N k).card then 1 else 0) +
          (if (f (n + k)).Nonempty then 1 else 0)) := Finset.sum_le_sum hNk
      _ = E2.card + Ene.card := by
        rw [Finset.sum_add_distrib, hE2, hEne, Finset.card_filter, Finset.card_filter]
  have hUcard : U.card ≤ E2.card + Ene.card + 1 := by
    have hins : U.card ≤ (E.biUnion N).card + 1 := Finset.card_insert_le (n + r) (E.biUnion N)
    omega
  have hmem : ∀ w, (f w).Nonempty → (w = n + r ∨ ∃ k' ∈ E, w ∈ (g k').inputs) → w ∈ U := by
    rintro w hw (h | ⟨k', hk', hin⟩)
    · rw [h]
      exact Finset.mem_insert_self _ _
    · refine Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨k', hk', ?_⟩)
      simp only [hN, Finset.mem_filter, List.mem_toFinset]
      exact ⟨hin, hw⟩
  have hRU : ∀ k, k ∈ R → n + k = n + r ∨ ∃ k' ∈ E, n + k ∈ (g k').inputs := by
    intro k hk
    rcases Relation.ReflTransGen.cases_tail ((hR k).1 hk) with h | ⟨b, hb, hb1, hb2, hb3⟩
    · left
      rw [h]
    · right
      refine ⟨b, ?_, hb3⟩
      rw [hE, Finset.mem_filter]
      exact ⟨(hR b).2 hb, hb1, hb2⟩
  set S2 : Finset ℕ := Ene.image (fun k => n + k) with hS2
  have hS2card : S2.card = Ene.card :=
    Finset.card_image_of_injective _ (fun a b h => Nat.add_left_cancel h)
  have hdisj : Disjoint (stops.filter (fun w => (f w).Nonempty)) S2 := by
    rw [Finset.disjoint_left]
    intro w hw hw2
    rw [Finset.mem_filter] at hw
    rw [hS2, Finset.mem_image] at hw2
    obtain ⟨k, hk, rfl⟩ := hw2
    rw [hEne, hE, Finset.mem_filter, Finset.mem_filter] at hk
    rcases (hstops _).1 hw.1 with ⟨h1, _⟩ | ⟨_, _, h3⟩
    · omega
    · rw [Nat.add_sub_cancel_left] at h3
      rcases h3 with h3 | h3
      · exact hk.1.2.1 h3
      · exact h3 hk.1.2.2
  have hsub : (stops.filter (fun w => (f w).Nonempty)) ∪ S2 ⊆ U := by
    intro w hw
    rcases Finset.mem_union.1 hw with hw | hw
    · rw [Finset.mem_filter] at hw
      rcases (hstops _).1 hw.1 with ⟨_, k, hk, hk1, hk2, hk3⟩ | ⟨h1, h2, _⟩
      · refine hmem w hw.2 (Or.inr ⟨k, ?_, hk3⟩)
        rw [hE, Finset.mem_filter]
        exact ⟨hk, hk1, hk2⟩
      · have := hRU _ h2
        rw [Nat.add_sub_cancel' h1] at this
        exact hmem w hw.2 this
    · rw [hS2, Finset.mem_image] at hw
      obtain ⟨k, hk, rfl⟩ := hw
      rw [hEne, hE, Finset.mem_filter, Finset.mem_filter] at hk
      exact hmem _ hk.2 (hRU k hk.1.1)
  have h3 := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, hS2card] at h3
  have h4 := Finset.card_le_card hE2I
  omega
theorem top_step2 (n : ℕ) (g : ℕ → Gate)
    (hlen : ∀ k, (g k).op = GateOp.or → (g k).inputs.length ≤ 2)
    (hback : ∀ k, ∀ i ∈ (g k).inputs, i < n + k)
    (f : ℕ → Finset (Fin n))
    (hf1 : ∀ w, w < n → (f w).card ≤ 1)
    (hf2 : ∀ k, (g k).op = GateOp.or →
      ∀ u, u ∈ f (n + k) ↔ ∃ w ∈ (g k).inputs, u ∈ f w)
    (hf3 : ∀ k, (g k).op ≠ GateOp.or → (f (n + k)).card ≤ 1)
    (Z : Finset ℕ) (ρ : ℕ) (c : Fin n) (E0 : Finset (Sym2 (Fin n)))
    (hZ : ∀ k, k ∈ Z → f (n + k) ⊆ f ρ →
      (∀ v, v ∈ f (n + k) → s(c, v) ∈ E0) ∨ (f (n + k)).card ≤ 1) :
    ∃ Znew : Finset ℕ, Disjoint Z Znew ∧
      (∀ k, k ∈ Znew → (g k).op = GateOp.or ∧ TwoNe g f k ∧ n ≤ ρ ∧
        Relation.ReflTransGen (fun k k' : ℕ =>
          (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) (ρ - n) k ∧ f (n + k) ⊆ f ρ) ∧
      (((f ρ).image (fun v => s(c, v))) \ E0).card ≤ Znew.card + 1 := by
  classical
  by_cases hρ : ρ < n
  · refine ⟨∅, Finset.disjoint_empty_right _, by simp, ?_⟩
    calc (((f ρ).image (fun v => s(c, v))) \ E0).card
        ≤ ((f ρ).image (fun v => s(c, v))).card := Finset.card_le_card Finset.sdiff_subset
      _ ≤ (f ρ).card := Finset.card_image_le
      _ ≤ 1 := hf1 ρ hρ
      _ ≤ (∅ : Finset ℕ).card + 1 := by simp
  · have hρn : n ≤ ρ := Nat.le_of_not_lt hρ
    obtain ⟨r, rfl⟩ : ∃ r, ρ = n + r := ⟨ρ - n, by omega⟩
    have hle : ∀ k, Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
        (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k → k ≤ r := by
      intro k h
      induction h with
      | refl => exact le_refl _
      | tail _ hbc ih =>
        have := hback _ _ hbc.2.2
        omega
    set R : Finset ℕ := (Finset.range (r + 1)).filter (fun k =>
      Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
        (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k) with hRdef
    have hR : ∀ k, k ∈ R ↔ Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
        (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k := by
      intro k
      rw [hRdef, Finset.mem_filter, Finset.mem_range]
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨Nat.lt_succ_of_le (hle k h), h⟩
    set stops : Finset ℕ := (Finset.range (n + r + 1)).filter (fun w =>
      (w < n ∧ ∃ k ∈ R, k ∉ Z ∧ (g k).op = GateOp.or ∧ w ∈ (g k).inputs) ∨
      (n ≤ w ∧ w - n ∈ R ∧ (w - n ∈ Z ∨ (g (w - n)).op ≠ GateOp.or))) with hsdef
    have hstops : ∀ w, w ∈ stops ↔
        (w < n ∧ ∃ k ∈ R, k ∉ Z ∧ (g k).op = GateOp.or ∧ w ∈ (g k).inputs) ∨
        (n ≤ w ∧ w - n ∈ R ∧ (w - n ∈ Z ∨ (g (w - n)).op ≠ GateOp.or)) := by
      intro w
      rw [hsdef, Finset.mem_filter, Finset.mem_range]
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨?_, h⟩
        rcases h with ⟨h1, _⟩ | ⟨h1, h2, _⟩
        · omega
        · have := hle _ ((hR _).1 h2)
          omega
    set Znew : Finset ℕ := R.filter (fun k => k ∉ Z ∧ (g k).op = GateOp.or ∧ TwoNe g f k)
      with hZn
    obtain ⟨hcov, hup⟩ := cover_g n g hback f hf2 Z r R hR stops hstops
    have hcnt : (stops.filter (fun w => (f w).Nonempty)).card ≤ Znew.card + 1 :=
      cone_count2 n g f hf2 Z (fun k _ h => hlen k h) r R hR stops hstops Znew (by
        intro k hk hkZ hor htwo
        rw [hZn, Finset.mem_filter]
        exact ⟨hk, hkZ, hor, htwo⟩)
    refine ⟨Znew, ?_, ?_, ?_⟩
    · rw [Finset.disjoint_left]
      intro k hk hk2
      rw [hZn, Finset.mem_filter] at hk2
      exact hk2.2.1 hk
    · intro k hk
      rw [hZn, Finset.mem_filter] at hk
      refine ⟨hk.2.2.1, hk.2.2.2, hρn, ?_, hup k hk.1⟩
      rw [Nat.add_sub_cancel_left]
      have hreach : ∀ k, Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
          (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k →
          Relation.ReflTransGen (fun k k' : ℕ =>
            (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k := by
        intro k h
        induction h with
        | refl => exact Relation.ReflTransGen.refl
        | tail _ hbc ih => exact ih.tail hbc.2
      exact hreach k ((hR k).1 hk.1)
    · have hsub : ((f (n + r)).image (fun v => s(c, v))) \ E0 ⊆
          (stops.filter (fun w => (f w).Nonempty)).biUnion
            (fun w => ((f w).image (fun v => s(c, v))) \ E0) := by
        intro e he
        rw [Finset.mem_sdiff, Finset.mem_image] at he
        obtain ⟨⟨v, hv, rfl⟩, he0⟩ := he
        obtain ⟨w, hw, hvw⟩ := Finset.mem_biUnion.1 (hcov hv)
        refine Finset.mem_biUnion.2 ⟨w, Finset.mem_filter.2 ⟨hw, ⟨v, hvw⟩⟩, ?_⟩
        rw [Finset.mem_sdiff]
        exact ⟨Finset.mem_image_of_mem _ hvw, he0⟩
      have hone : ∀ w, w ∈ stops.filter (fun w => (f w).Nonempty) →
          (((f w).image (fun v => s(c, v))) \ E0).card ≤ 1 := by
        intro w hw'
        have hw := (Finset.mem_filter.1 hw').1
        have himg : ∀ t : Finset (Fin n), t.card ≤ 1 →
            ((t.image (fun v => s(c, v))) \ E0).card ≤ 1 := fun t ht =>
          (Finset.card_le_card Finset.sdiff_subset).trans (Finset.card_image_le.trans ht)
        rcases (hstops w).1 hw with ⟨hwn, _⟩ | ⟨hwn, hwR, hw2⟩
        · exact himg _ (hf1 w hwn)
        · have hweq : n + (w - n) = w := by omega
          rcases hw2 with hz | hnor
          · have hsubw : f (n + (w - n)) ⊆ f (n + r) := hup _ hwR
            rcases hZ _ hz hsubw with hall | hc1
            · rw [hweq] at hall
              have hempty : ((f w).image (fun v => s(c, v))) \ E0 = ∅ := by
                rw [Finset.sdiff_eq_empty_iff_subset]
                intro e he
                obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 he
                exact hall v hv
              rw [hempty]
              simp
            · rw [hweq] at hc1
              exact himg _ hc1
          · have := hf3 _ hnor
            rw [hweq] at this
            exact himg _ this
      calc (((f (n + r)).image (fun v => s(c, v))) \ E0).card
          ≤ ((stops.filter (fun w => (f w).Nonempty)).biUnion
              (fun w => ((f w).image (fun v => s(c, v))) \ E0)).card :=
            Finset.card_le_card hsub
        _ ≤ (stops.filter (fun w => (f w).Nonempty)).card * 1 :=
            Finset.card_biUnion_le_card_mul _ _ _ hone
        _ ≤ Znew.card + 1 := by omega
theorem star_count2 (n : ℕ) (G : SimpleGraph (Fin n))
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (g : ℕ → Gate)
    (hlen : ∀ k, (g k).op = GateOp.or → (g k).inputs.length ≤ 2)
    (hback : ∀ k, ∀ i ∈ (g k).inputs, i < n + k)
    (f : ℕ → Finset (Fin n))
    (hf1 : ∀ w, w < n → (f w).card ≤ 1)
    (hf2 : ∀ k, (g k).op = GateOp.or →
      ∀ u, u ∈ f (n + k) ↔ ∃ w ∈ (g k).inputs, u ∈ f w)
    (hf3 : ∀ k, (g k).op ≠ GateOp.or → (f (n + k)).card ≤ 1)
    (B : Finset ℕ) (hB : ∀ k, k ∈ B → (f (n + k)).card ≤ 1)
    (l : List (Fin n × ℕ))
    (hadj : ∀ p, p ∈ l → ∀ v, v ∈ f p.2 → G.Adj p.1 v) :
    ∃ Z : Finset ℕ,
      (∀ k, k ∈ Z → k ∉ B ∧ (g k).op = GateOp.or ∧ TwoNe g f k ∧ ∃ p, p ∈ l ∧ n ≤ p.2 ∧
        Relation.ReflTransGen (fun k k' : ℕ =>
          (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) (p.2 - n) k ∧ f (n + k) ⊆ f p.2) ∧
      (l.toFinset.biUnion (fun p => (f p.2).image (fun v => s(p.1, v)))).card
        ≤ l.length + Z.card := by
  classical
  induction l with
  | nil => exact ⟨∅, by simp, by simp⟩
  | cons p l ih =>
    obtain ⟨Z, hZ1, hZ2⟩ := ih (fun q hq => hadj q (List.mem_cons_of_mem _ hq))
    set E0 := l.toFinset.biUnion (fun p => (f p.2).image (fun v => s(p.1, v))) with hE0
    obtain ⟨Znew, hd, hn1, hn2⟩ := top_step2 n g hlen hback f hf1 hf2 hf3 (Z ∪ B) p.2 p.1 E0 (by
      intro k hk hsub
      rcases Finset.mem_union.1 hk with hk | hk
      · obtain ⟨_, _, _, q, hq, _, _, hfq⟩ := hZ1 k hk
        by_cases hc : q.1 = p.1
        · left
          intro v hv
          rw [hE0]
          refine Finset.mem_biUnion.2 ⟨q, List.mem_toFinset.2 hq, ?_⟩
          rw [← hc]
          exact Finset.mem_image_of_mem _ (hfq hv)
        · right
          by_contra hcard
          have h2 : 1 < (f (n + k)).card := by omega
          obtain ⟨v, hv, v', hv', hne⟩ := Finset.one_lt_card.1 h2
          have a1 : G.Adj p.1 v := hadj p List.mem_cons_self v (hsub hv)
          have a2 : G.Adj p.1 v' := hadj p List.mem_cons_self v' (hsub hv')
          have b1 : G.Adj q.1 v := hadj q (List.mem_cons_of_mem _ hq) v (hfq hv)
          have b2 : G.Adj q.1 v' := hadj q (List.mem_cons_of_mem _ hq) v' (hfq hv')
          exact h4 p.1 v q.1 v' (fun h => hc h.symm) hne ⟨a1, b1.symm, b2, a2.symm⟩
      · exact Or.inr (hB k hk))
    have hd1 : Disjoint Z Znew := Finset.disjoint_of_subset_left Finset.subset_union_left hd
    refine ⟨Z ∪ Znew, ?_, ?_⟩
    · intro k hk
      rcases Finset.mem_union.1 hk with hk | hk
      · obtain ⟨h0, h1, ht, q, hq, h2⟩ := hZ1 k hk
        exact ⟨h0, h1, ht, q, List.mem_cons_of_mem _ hq, h2⟩
      · obtain ⟨h1, ht, h2, h3, h5⟩ := hn1 k hk
        refine ⟨?_, h1, ht, p, List.mem_cons_self, h2, h3, h5⟩
        intro hkB
        exact (Finset.disjoint_left.1 hd (Finset.mem_union_right _ hkB)) hk
    · rw [List.toFinset_cons, Finset.biUnion_insert, Finset.card_union_of_disjoint hd1,
        List.length_cons, ← hE0]
      have hsplit : (f p.2).image (fun v => s(p.1, v)) ∪ E0 =
          (((f p.2).image (fun v => s(p.1, v))) \ E0) ∪ E0 := by
        rw [Finset.sdiff_union_self_eq_union]
      have hle := Finset.card_union_le (((f p.2).image (fun v => s(p.1, v))) \ E0) E0
      rw [← hsplit] at hle
      omega
theorem assemble2 (n : ℕ) (G : SimpleGraph (Fin n))
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (g : ℕ → Gate)
    (hlen : ∀ k, (g k).op = GateOp.or → (g k).inputs.length ≤ 2)
    (hback : ∀ k, ∀ i ∈ (g k).inputs, i < n + k)
    (f : ℕ → Finset (Fin n))
    (hf1 : ∀ w, w < n → (f w).card ≤ 1)
    (hf2 : ∀ k, (g k).op = GateOp.or →
      ∀ u, u ∈ f (n + k) ↔ ∃ w ∈ (g k).inputs, u ∈ f w)
    (hf3 : ∀ k, (g k).op ≠ GateOp.or → (f (n + k)).card ≤ 1)
    (B : Finset ℕ) (hB : ∀ k, k ∈ B → (f (n + k)).card ≤ 1)
    (T : Finset ℕ) (o : ℕ → Fin 2 → ℕ)
    (hstar : ∀ a, a ∈ T → (∀ u, u ∈ f (o a 0) → ∀ v, v ∈ f (o a 1) → G.Adj u v) ∧
      ((f (o a 0)).card ≤ 1 ∨ (f (o a 1)).card ≤ 1))
    (Es : Finset (Sym2 (Fin n)))
    (hEs : ∀ e, e ∈ Es → ∃ a, a ∈ T ∧ ∃ u, u ∈ f (o a 0) ∧ ∃ v, v ∈ f (o a 1) ∧ e = s(u, v)) :
    (∃ Z : Finset ℕ,
      (∀ k, k ∈ Z → k ∉ B ∧ (g k).op = GateOp.or ∧ TwoNe g f k ∧ ∃ a, a ∈ T ∧ ∃ b : Fin 2,
        n ≤ o a b ∧
        Relation.ReflTransGen (fun k k' : ℕ =>
          (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) (o a b - n) k ∧
        f (n + k) ⊆ f (o a b) ∧ (f (o a (1 - b))).card = 1) ∧
      Es.card ≤ T.card + Z.card) ∧
    ∀ (H : SimpleGraph (Fin n)) (K : Finset (Fin n)),
      (∀ u v : Fin n, H.Adj u v → s(u, v) ∈ Es) → IsMinCover H K → K.card ≤ T.card := by
  classical
  by_cases hEe : Es = ∅
  · subst hEe
    refine ⟨⟨∅, by simp, by simp⟩, ?_⟩
    intro H K hH hK
    have h0 := hK.2 ∅ (by
      intro u v huv
      exact absurd (hH u v huv) (Finset.notMem_empty _))
    simp only [Finset.card_empty] at h0
    omega
  · obtain ⟨e0, he0⟩ := Finset.nonempty_iff_ne_empty.2 hEe
    obtain ⟨_, _, v0, _, _⟩ := hEs e0 he0
    set c : ℕ → Fin n := fun a =>
      if (f (o a 0)).card ≤ 1 then (if h : (f (o a 0)).Nonempty then h.choose else v0)
      else (if h : (f (o a 1)).Nonempty then h.choose else v0) with hc
    set ρ : ℕ → ℕ := fun a => if (f (o a 0)).card ≤ 1 then o a 1 else o a 0 with hρ
    have hkey : ∀ a, a ∈ T → ∀ u, u ∈ f (o a 0) → ∀ v, v ∈ f (o a 1) →
        (c a = u ∧ v ∈ f (ρ a)) ∨ (c a = v ∧ u ∈ f (ρ a)) := by
      intro a ha u hu v hv
      by_cases h0 : (f (o a 0)).card ≤ 1
      · left
        have hne : (f (o a 0)).Nonempty := ⟨u, hu⟩
        refine ⟨?_, ?_⟩
        · simp only [hc, h0, ↓reduceIte, hne, ↓reduceDIte]
          exact Finset.card_le_one.1 h0 _ hne.choose_spec _ hu
        · simp only [hρ, h0, ↓reduceIte]
          exact hv
      · right
        have h1 : (f (o a 1)).card ≤ 1 := by
          rcases (hstar a ha).2 with h | h
          · exact absurd h h0
          · exact h
        have hne : (f (o a 1)).Nonempty := ⟨v, hv⟩
        refine ⟨?_, ?_⟩
        · simp only [hc, h0, ↓reduceIte, hne, ↓reduceDIte]
          exact Finset.card_le_one.1 h1 _ hne.choose_spec _ hv
        · simp only [hρ, h0, ↓reduceIte]
          exact hu
    set T' : Finset ℕ := T.filter (fun a => (f (o a 0)).Nonempty ∧ (f (o a 1)).Nonempty)
      with hT'
    have hT'T : ∀ a, a ∈ T' → a ∈ T := fun a ha => (Finset.mem_filter.1 ha).1
    have hT'card : T'.card ≤ T.card := Finset.card_le_card (Finset.filter_subset _ _)
    have hadjc : ∀ a, a ∈ T' → ∀ v, v ∈ f (ρ a) → G.Adj (c a) v := by
      intro a ha' v hv
      have ha := hT'T a ha'
      have hnn := (Finset.mem_filter.1 ha').2
      by_cases h0 : (f (o a 0)).card ≤ 1
      · simp only [hρ, h0, ↓reduceIte] at hv
        have hne := hnn.1
        simp only [hc, h0, ↓reduceIte, hne, ↓reduceDIte]
        exact (hstar a ha).1 _ hne.choose_spec v hv
      · simp only [hρ, h0, ↓reduceIte] at hv
        have hne := hnn.2
        simp only [hc, h0, ↓reduceIte, hne, ↓reduceDIte]
        exact ((hstar a ha).1 v hv _ hne.choose_spec).symm
    have hEs' : ∀ e, e ∈ Es → ∃ a, a ∈ T' ∧ ∃ v, v ∈ f (ρ a) ∧ e = s(c a, v) := by
      intro e he
      obtain ⟨a, ha, u, hu, v, hv, rfl⟩ := hEs e he
      have ha' : a ∈ T' := Finset.mem_filter.2 ⟨ha, ⟨u, hu⟩, ⟨v, hv⟩⟩
      rcases hkey a ha u hu v hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨a, ha', v, h2, by rw [h1]⟩
      · exact ⟨a, ha', u, h2, by rw [h1]; exact Sym2.eq_swap⟩
    refine ⟨?_, ?_⟩
    · obtain ⟨Z, hZ1, hZ2⟩ := star_count2 n G h4 g hlen hback f hf1 hf2 hf3 B hB
        (T'.toList.map (fun a => (c a, ρ a))) (by
          intro p hp v hv
          obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hp
          exact hadjc a (Finset.mem_toList.1 ha) v hv)
      refine ⟨Z, ?_, ?_⟩
      · intro k hk
        obtain ⟨h1, h2, ht, p, hp, h3, h5, h6⟩ := hZ1 k hk
        obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hp
        have ha' := Finset.mem_toList.1 ha
        have hnn := (Finset.mem_filter.1 ha').2
        refine ⟨h1, h2, ht, a, hT'T a ha', ?_⟩
        by_cases h0 : (f (o a 0)).card ≤ 1
        · refine ⟨1, ?_⟩
          simp only [hρ, h0, ↓reduceIte] at h3 h5 h6
          have e : (1 - 1 : Fin 2) = 0 := by decide
          rw [e]
          exact ⟨h3, h5, h6, le_antisymm h0 (Finset.card_pos.2 hnn.1)⟩
        · refine ⟨0, ?_⟩
          simp only [hρ, h0, ↓reduceIte] at h3 h5 h6
          have e : (1 - 0 : Fin 2) = 1 := by decide
          rw [e]
          have h1' : (f (o a 1)).card ≤ 1 := by
            rcases (hstar a (hT'T a ha')).2 with h | h
            · exact absurd h h0
            · exact h
          exact ⟨h3, h5, h6, le_antisymm h1' (Finset.card_pos.2 hnn.2)⟩
      · have hsub : Es ⊆ (T'.toList.map (fun a => (c a, ρ a))).toFinset.biUnion
            (fun p => (f p.2).image (fun v => s(p.1, v))) := by
          intro e he
          obtain ⟨a, ha, v, hv, rfl⟩ := hEs' e he
          refine Finset.mem_biUnion.2 ⟨(c a, ρ a), ?_, Finset.mem_image_of_mem _ hv⟩
          exact List.mem_toFinset.2 (List.mem_map.2 ⟨a, Finset.mem_toList.2 ha, rfl⟩)
        have h1 := Finset.card_le_card hsub
        rw [List.length_map, Finset.length_toList] at hZ2
        omega
    · intro H K hH hK
      refine (cover_bound n H T' c ?_ K hK).trans hT'card
      intro u v huv
      obtain ⟨a, ha, w, hw, he⟩ := hEs' _ (hH u v huv)
      refine ⟨a, ha, ?_⟩
      have := Sym2.eq_iff.1 he
      rcases this with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact Or.inl h1.symm
      · exact Or.inr h2.symm
lemma gateAt_ge {C : Circuit} {k : ℕ} (hk : C.gates.length ≤ k) :
    gateAt C k = ⟨GateOp.or, []⟩ := by
  unfold gateAt
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hk]
lemma orIn_iff_reach {n : ℕ} {C : Circuit} (p : ℕ) (u : Fin n) :
    u ∈ PEqualNP.TopForm.orIn n C p ↔ Relation.ReflTransGen (S90.OrStep n C) p u.val :=
  ⟨S90.mem_orIn_reach u, S90.reach_mem_orIn u⟩
lemma orIn_input {n : ℕ} (C : Circuit) (w : ℕ) (hw : w < n) :
    (PEqualNP.TopForm.orIn n C w).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  rw [orIn_iff_reach] at ha hb
  have h1 : ∀ c : Fin n, Relation.ReflTransGen (S90.OrStep n C) w c.val → c.val = w := by
    intro c hc
    rcases Relation.ReflTransGen.cases_head hc with h | ⟨d, hd, _⟩
    · exact h.symm
    · obtain ⟨k, _, h3, _⟩ := hd
      omega
  exact Fin.ext ((h1 a ha).trans (h1 b hb).symm)
lemma orIn_gate {n : ℕ} (C : Circuit) (k : ℕ) (u : Fin n) :
    u ∈ PEqualNP.TopForm.orIn n C (n + k) ↔ k < C.gates.length ∧
      (gateAt C k).op = GateOp.or ∧ ∃ w ∈ (gateAt C k).inputs, w < n + k ∧
        u ∈ PEqualNP.TopForm.orIn n C w := by
  rw [orIn_iff_reach]
  constructor
  · intro h
    rcases Relation.ReflTransGen.cases_head h with h | ⟨d, hd, hr⟩
    · have := u.isLt
      omega
    · obtain ⟨k', hk', he, hop, hin, hlt⟩ := hd
      have hkk : k' = k := by omega
      subst hkk
      exact ⟨hk', hop, d, hin, hlt, (orIn_iff_reach d u).2 hr⟩
  · rintro ⟨hk, hop, w, hw, hlt, hu⟩
    exact Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hw, hlt⟩ ((orIn_iff_reach w u).1 hu)
lemma junk_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (k : ℕ) :
    k ∈ PEqualNP.TopForm.junk G C ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧
      ¬ PEqualNP.TopForm.BelowF G C k := by
  unfold PEqualNP.TopForm.junk PEqualNP.TopForm.gatesWhere
  simp only [Finset.mem_filter, Finset.mem_range]
  unfold PEqualNP.CleanedNonEdge.IsDirtyAnd PEqualNP.CleanedNonEdge.IsDirty
  constructor
  · rintro ⟨h1, h2, _, x, hx1, hx2⟩
    refine ⟨h1, h2, fun h => ?_⟩
    have h3 := h x hx1
    rw [hx2] at h3
    exact absurd h3 (by simp)
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, h1, ?_⟩
    by_contra hc
    apply h3
    intro x hx
    by_contra hf
    exact hc ⟨x, hx, by simpa using hf⟩
lemma opnd_lt {n : ℕ} {C : Circuit} (h2 : ∀ g ∈ C.gates, g.inputs.length = 2)
    (hRB : ReadsBack n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    PEqualNP.TopForm.opnd C a b < n + a := by
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 _ (S90.gateAt_mem ha))
  have hp : p < n + a := hRB a ha p (by rw [hin]; simp)
  have hq : q < n + a := hRB a ha q (by rw [hin]; simp)
  fin_cases b
  · simpa [PEqualNP.TopForm.opnd, hin] using hp
  · simpa [PEqualNP.TopForm.opnd, hin] using hq
lemma rtg_conv {n : ℕ} (C : Circuit) (hRB : ReadsBack n C) (r k : ℕ)
    (h : Relation.ReflTransGen (fun k k' : ℕ =>
      (gateAt C k).op = GateOp.or ∧ n + k' ∈ (gateAt C k).inputs) r k)
    (hr : r < C.gates.length) :
    Relation.ReflTransGen (S90.OrStep n C) (n + r) (n + k) ∧ k < C.gates.length := by
  induction h with
  | refl => exact ⟨Relation.ReflTransGen.refl, hr⟩
  | tail _ hbc ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hlt := hRB _ ih2 _ hbc.2
    exact ⟨ih1.tail ⟨_, ih2, rfl, hbc.1, hbc.2, hlt⟩, by omega⟩
lemma two_facts {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h2 : ∀ g ∈ C.gates, g.inputs.length = 2) (hRB : ReadsBack n C) {k : ℕ}
    (hk : k < C.gates.length) (hor : (gateAt C k).op = GateOp.or)
    (htwo : TwoNe (gateAt C) (PEqualNP.TopForm.orIn n C) k) :
    ¬ PEqualNP.TopForm.BelowF G C k ∧
      (PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C k 0)).Nonempty ∧
      (PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C k 1)).Nonempty := by
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 _ (S90.gateAt_mem hk))
  have e0 : PEqualNP.TopForm.opnd C k 0 = p := by simp [PEqualNP.TopForm.opnd, hin]
  have e1 : PEqualNP.TopForm.opnd C k 1 = q := by simp [PEqualNP.TopForm.opnd, hin]
  obtain ⟨w1, hw1, w2, hw2, hne, hn1, hn2⟩ := htwo
  have hw1lt : w1 < n + k := hRB k hk w1 hw1
  have hw1m := hw1
  rw [hin] at hw1 hw2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw1 hw2
  refine ⟨?_, ?_⟩
  · intro hbel
    obtain ⟨u, hu⟩ := hn1
    have hu2 : u ∈ PEqualNP.TopForm.orIn n C (n + k) :=
      (orIn_gate C k u).2 ⟨hk, hor, w1, hw1m, hw1lt, hu⟩
    have hr := (orIn_iff_reach _ u).1 hu2
    have hv := S90.reach_var_val (PEqualNP.EdgeOwnership.pairInput u u) (n + k) u hr
      (S90.pairInput_left u u)
    have hF := hbel _ (by rw [S90.gateVal_eq_val]; exact hv)
    exact G.irrefl ((S90.graphFun_pair G u u).1 hF)
  · rw [e0, e1]
    rcases hw1 with h1 | h1 <;> rcases hw2 with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · rw [h1] at hn1
      rw [h2] at hn2
      exact ⟨hn1, hn2⟩
    · rw [h1] at hn1
      rw [h2] at hn2
      exact ⟨hn2, hn1⟩
    · exact absurd (h1.trans h2.symm) hne
theorem main (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : PEqualNP.TopForm.NoFourCycle G) (hne : G.edgeFinset.Nonempty)
    (hL : PEqualNP.TopForm.IsLeastAO G C) (hTF : PEqualNP.TopForm.TopForm G C) :
    G.edgeFinset.card + (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card +
        2 * (PEqualNP.TopForm.centreless G C).card + (PEqualNP.TopForm.junk G C).card +
        (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card ≤
      C.size + (PEqualNP.TopForm.Ustar G C).card + 1 ∧
    ∀ K : Finset (Fin n),
      PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑(PEqualNP.TopForm.Ustar G C)) K →
      K.card ≤ (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card := by
  classical
  obtain ⟨⟨hAO, hRB, h2⟩, _, _⟩ := id hL
  have hlen : ∀ k, (gateAt C k).op = GateOp.or → (gateAt C k).inputs.length ≤ 2 := by
    intro k _
    by_cases hk : k < C.gates.length
    · rw [h2 _ (S90.gateAt_mem hk)]
    · rw [gateAt_ge (by omega)]
      simp
  have hback : ∀ k, ∀ i ∈ (gateAt C k).inputs, i < n + k := by
    intro k i hi
    by_cases hk : k < C.gates.length
    · exact hRB k hk i hi
    · rw [gateAt_ge (by omega)] at hi
      simp at hi
  have hf2 : ∀ k, (gateAt C k).op = GateOp.or → ∀ u,
      u ∈ PEqualNP.TopForm.orIn n C (n + k) ↔
        ∃ w ∈ (gateAt C k).inputs, u ∈ PEqualNP.TopForm.orIn n C w := by
    intro k hop u
    rw [orIn_gate]
    constructor
    · rintro ⟨_, _, w, hw, _, hu⟩
      exact ⟨w, hw, hu⟩
    · rintro ⟨w, hw, hu⟩
      have hk : k < C.gates.length := by
        by_contra hk
        rw [gateAt_ge (by omega)] at hw
        simp at hw
      exact ⟨hk, hop, w, hw, hRB k hk w hw, hu⟩
  have hf3 : ∀ k, (gateAt C k).op ≠ GateOp.or →
      (PEqualNP.TopForm.orIn n C (n + k)).card ≤ 1 := by
    intro k hop
    rw [Finset.card_le_one]
    intro a ha
    exact absurd ((orIn_gate C k a).1 ha).2.1 hop
  have h4' : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) := by
    rintro a b c d hac hbd ⟨h1, h2', h3, h5⟩
    have hsub : ({b, d} : Finset (Fin n)) ⊆
        Finset.univ.filter (fun w => G.Adj a w ∧ G.Adj c w) := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hw with rfl | rfl
      · exact ⟨h1, h2'.symm⟩
      · exact ⟨h5.symm, h3⟩
    have := (Finset.card_le_card hsub).trans (h4 a c hac)
    rw [Finset.card_pair hbd] at this
    omega
  have hstar : ∀ a, a ∈ PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C →
      (∀ u, u ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 0) →
        ∀ v, v ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 1) → G.Adj u v) ∧
      ((PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 0)).card ≤ 1 ∨
        (PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 1)).card ≤ 1) := by
    intro a ha
    have hf := S90.top_facts G C h4 hL a (Finset.mem_sdiff.1 ha).1
    exact ⟨hf.2.1, hf.2.2⟩
  have hEs : ∀ e, e ∈ G.edgeFinset \ PEqualNP.TopForm.Ustar G C →
      ∃ a, a ∈ PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C ∧
        ∃ u, u ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 0) ∧
        ∃ v, v ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 1) ∧ e = s(u, v) := by
    intro e he
    have he' : e ∈ PEqualNP.TopForm.starEdges G C := by
      simp only [PEqualNP.TopForm.Ustar, Finset.mem_sdiff, not_and, not_not] at he
      exact he.2 he.1
    simp only [PEqualNP.TopForm.starEdges, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_product] at he'
    obtain ⟨a, ha, p, hp, hpe⟩ := he'
    refine ⟨a, ?_, p.1, hp.1, p.2, hp.2, hpe.symm⟩
    rw [Finset.mem_sdiff]
    refine ⟨ha, fun hc => ?_⟩
    simp only [PEqualNP.TopForm.centreless, Finset.mem_filter] at hc
    rcases hc.2 with h | h
    · have := hp.1
      rw [h] at this
      exact absurd this (Finset.notMem_empty _)
    · have := hp.2
      rw [h] at this
      exact absurd this (Finset.notMem_empty _)
  obtain ⟨⟨Z, hZ1, hZ2⟩, hcov⟩ := assemble2 n G h4' (gateAt C) hlen hback
    (fun w => PEqualNP.TopForm.orIn n C w) (fun w hw => orIn_input C w hw) hf2 hf3 ∅ (by simp)
    (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C) (PEqualNP.TopForm.opnd C)
    hstar (G.edgeFinset \ PEqualNP.TopForm.Ustar G C) hEs
  refine ⟨?_, ?_⟩
  · have hZlam : Z ⊆ PEqualNP.TopForm.lam G C := by
      intro k hk
      obtain ⟨-, hor, htwo, a, ha, b, hnb, hrt, -, hcard⟩ := hZ1 k hk
      have hatop := (Finset.mem_sdiff.1 ha).1
      have halen : a < C.gates.length := by
        simp only [PEqualNP.TopForm.tops, PEqualNP.TopForm.gatesWhere, Finset.mem_filter,
          Finset.mem_range] at hatop
        exact hatop.1
      have hlt := opnd_lt h2 hRB halen b
      obtain ⟨hreach, hklen⟩ := rtg_conv C hRB _ k hrt (by omega)
      rw [show n + (PEqualNP.TopForm.opnd C a b - n) = PEqualNP.TopForm.opnd C a b by omega]
        at hreach
      have hOR := S90.reach_orReaches hreach k rfl hklen
      obtain ⟨hnbel, hn0, hn1⟩ := two_facts G C h2 hRB hklen hor htwo
      simp only [PEqualNP.TopForm.lam, PEqualNP.TopForm.orN, PEqualNP.TopForm.gatesWhere,
        Finset.mem_filter, Finset.mem_range]
      exact ⟨⟨hklen, hor, hnbel⟩, hn0, hn1, a, hatop, b, hcard, hOR⟩
    have hAO' : ∀ k, k < C.gates.length →
        ((gateAt C k).op = GateOp.and ∧ ¬ (gateAt C k).op = GateOp.or) ∨
        ((gateAt C k).op = GateOp.or ∧ ¬ (gateAt C k).op = GateOp.and) := by
      intro k hk
      rcases hAO _ (S90.gateAt_mem hk) with h | h
      · exact Or.inl ⟨h, fun h' => by rw [h] at h'; cases h'⟩
      · exact Or.inr ⟨h, fun h' => by rw [h] at h'; cases h'⟩
    have hsplit := four_split C.gates.length (fun k => (gateAt C k).op = GateOp.and)
      (fun k => (gateAt C k).op = GateOp.or) (fun k => PEqualNP.TopForm.BelowF G C k) hAO'
      (PEqualNP.TopForm.tops G C) (PEqualNP.TopForm.junk G C) (PEqualNP.TopForm.orT G C)
      (PEqualNP.TopForm.orN G C)
      (fun k => by simp only [PEqualNP.TopForm.tops, PEqualNP.TopForm.gatesWhere,
        Finset.mem_filter, Finset.mem_range])
      (fun k => junk_iff G C k)
      (fun k => by simp only [PEqualNP.TopForm.orT, PEqualNP.TopForm.gatesWhere,
        Finset.mem_filter, Finset.mem_range])
      (fun k => by simp only [PEqualNP.TopForm.orN, PEqualNP.TopForm.gatesWhere,
        Finset.mem_filter, Finset.mem_range])
    have hm := (S98.main_real n G C hne hL hTF).2.2
    have hsize : C.size = C.gates.length := rfl
    have hU := Finset.card_sdiff_add_card_eq_card
      (show PEqualNP.TopForm.Ustar G C ⊆ G.edgeFinset from Finset.sdiff_subset)
    have hTc := Finset.card_sdiff_add_card_eq_card
      (show PEqualNP.TopForm.centreless G C ⊆ PEqualNP.TopForm.tops G C from
        Finset.filter_subset _ _)
    have hlam := Finset.card_sdiff_add_card_eq_card
      (show PEqualNP.TopForm.lam G C ⊆ PEqualNP.TopForm.orN G C from
        Finset.filter_subset _ _)
    have hZl := Finset.card_le_card hZlam
    omega
  · intro K hK
    refine hcov _ K ?_ hK
    intro u v huv
    rw [SimpleGraph.deleteEdges_adj] at huv
    rw [Finset.mem_sdiff, SimpleGraph.mem_edgeFinset]
    exact ⟨huv.1, fun h => huv.2 (Finset.mem_coe.2 h)⟩
end P1
theorem prev1 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
  PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C →
  PEqualNP.TopForm.TopForm G C →
    G.edgeFinset.card + (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card +
        2 * (PEqualNP.TopForm.centreless G C).card + (PEqualNP.TopForm.junk G C).card +
        (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card ≤
      C.size + (PEqualNP.TopForm.Ustar G C).card + 1 ∧
    ∀ K : Finset (Fin n),
      PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑(PEqualNP.TopForm.Ustar G C)) K →
      K.card ≤ (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card := by
  intro n G _ C h4 hne hL hTF
  exact PEqualNP.Outside.L_meta_2448_aux.foundation.M1528.P1.main n G C h4 hne hL hTF
namespace P2
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
lemma fin2_sub : ∀ b : Fin 2, (b = 0 ∧ 1 - b = 1) ∨ (b = 1 ∧ 1 - b = 0) := by decide
lemma fin2_ne : ∀ b c : Fin 2, c ≠ b → c = 1 - b := by decide
lemma fin2_ne' : ∀ b c : Fin 2, c ≠ b → 1 - c = b := by decide
lemma fin2_both (p : Fin 2 → Prop) (b : Fin 2) (h1 : p b) (h2 : p (1 - b)) : p 0 ∧ p 1 := by
  rcases fin2_sub b with ⟨h, h'⟩ | ⟨h, h'⟩
  · rw [h] at h1; rw [h'] at h2; exact ⟨h1, h2⟩
  · rw [h] at h1; rw [h'] at h2; exact ⟨h2, h1⟩
lemma count_fibres {α β : Type*} [DecidableEq α] [DecidableEq β] (T : Finset α) (c : α → β)
    (P : Finset β)
    (hP : ∀ u ∈ P, ∃ a ∈ T, ∃ a' ∈ T, a ≠ a' ∧ c a = u ∧ c a' = u) :
    (T.image c).card + P.card ≤ T.card := by
  have hsub : P ⊆ T.image c := by
    intro u hu
    obtain ⟨a, ha, _, _, _, rfl, _⟩ := hP u hu
    exact Finset.mem_image_of_mem c ha
  have h1 : T.card = ∑ k ∈ T.image c, (T.filter (fun a => c a = k)).card :=
    Finset.card_eq_sum_card_image c T
  have h2 : (T.image c).card + P.card = ∑ k ∈ T.image c, (1 + if k ∈ P then 1 else 0) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one, ← Finset.card_filter]
    congr 2
    ext u
    simp only [Finset.mem_filter]
    exact ⟨fun h => ⟨hsub h, h⟩, fun h => h.2⟩
  rw [h1, h2]
  apply Finset.sum_le_sum
  intro k hk
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hk
  split_ifs with hkP
  · obtain ⟨a1, ha1, a2, ha2, hne, h1', h2'⟩ := hP _ hkP
    have : 1 < (T.filter (fun a' => c a' = c a)).card :=
      Finset.one_lt_card.mpr ⟨a1, by simp [ha1, h1'], a2, by simp [ha2, h2'], hne⟩
    omega
  · have : 0 < (T.filter (fun a' => c a' = c a)).card :=
      Finset.card_pos.mpr ⟨a, by simp [ha]⟩
    omega
theorem core {n : ℕ} (G : SimpleGraph (Fin n)) (tops centreless : Finset ℕ)
    (side : ℕ → Fin 2 → Finset (Fin n)) (R : ℕ → Fin 2 → Prop) (W : Finset (Fin n))
    (starEdges Ustar : Finset (Sym2 (Fin n)))
    (H1 : ∀ a ∈ tops, a ∈ centreless → (side a 0 = ∅ ∨ side a 1 = ∅))
    (H2 : ∀ a ∈ tops, (side a 0).card ≤ 1 ∨ (side a 1).card ≤ 1)
    (H3 : ∀ a ∈ tops, ¬ (R a 0 ∧ R a 1))
    (H4 : ∀ a ∈ tops, ∀ b : Fin 2, side a b = ∅ → R a b)
    (H5 : ∀ e ∈ starEdges, ∃ a ∈ tops, ∃ u ∈ side a 0, ∃ v ∈ side a 1, e = s(u, v))
    (H6 : ∀ u v, G.Adj u v → s(u, v) ∉ Ustar → s(u, v) ∈ starEdges)
    (H7 : ∀ a ∈ tops, ∀ (b : Fin 2) (u : Fin n), side a b = {u} → R a b →
      side a (1 - b) ⊆ W) :
    ∃ K : Finset (Fin n), (∀ e ∈ starEdges, ∃ v ∈ K, v ∈ e) ∧
      (∀ u, (∃ a ∈ tops, ∃ b : Fin 2, side a b = {u} ∧ R a b) → u ∈ K) ∧
      (∀ w, (∃ a ∈ tops, ∃ b : Fin 2, 2 ≤ (side a b).card ∧ R a b ∧ side a (1 - b) = {w}) →
        w ∈ K) ∧
      ∀ P : Finset (Fin n), (∀ u ∈ P, (∃ a ∈ tops, ∃ b : Fin 2, side a b = {u} ∧ R a b) ∧
          ∃ v, G.Adj u v ∧ s(u, v) ∉ Ustar ∧ v ∉ W ∧ v ∉ K) →
        K.card + P.card ≤ (tops \ centreless).card := by
  classical
  set T : Finset ℕ := tops.filter (fun a => (side a 0).Nonempty ∧ (side a 1).Nonempty) with hT
  have hTsub : T ⊆ tops \ centreless := by
    intro a ha
    obtain ⟨hat, h0, h1⟩ := Finset.mem_filter.mp ha
    refine Finset.mem_sdiff.mpr ⟨hat, fun hac => ?_⟩
    rcases H1 a hat hac with h | h
    · rw [h] at h0; exact Finset.not_nonempty_empty h0
    · rw [h] at h1; exact Finset.not_nonempty_empty h1
  have memT : ∀ a ∈ tops, ∀ b : Fin 2, (side a b).Nonempty → (side a (1 - b)).Nonempty →
      a ∈ T := by
    intro a hat b h1 h2
    exact Finset.mem_filter.mpr ⟨hat, fin2_both (fun b => (side a b).Nonempty) b h1 h2⟩
  have hA : ∀ a ∈ tops, ∀ (b : Fin 2) (u : Fin n), side a b = {u} → R a b → a ∈ T := by
    intro a hat b u hs hr
    refine memT a hat b (by rw [hs]; exact Finset.singleton_nonempty u) ?_
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    exact H3 a hat (fin2_both (fun b => R a b) b hr (H4 a hat _ he))
  have hex : ∀ a : {a // a ∈ T}, ∃ x : Fin n,
      (∃ b : Fin 2, side a.1 b = {x}) ∧
        ∀ (b : Fin 2) (u : Fin n), side a.1 b = {u} → R a.1 b → u = x := by
    rintro ⟨a, ha⟩
    obtain ⟨hat, h0, h1⟩ := Finset.mem_filter.mp ha
    by_cases hf : ∃ (b : Fin 2) (u : Fin n), side a b = {u} ∧ R a b
    · obtain ⟨b, u, hs, hr⟩ := hf
      refine ⟨u, ⟨b, hs⟩, ?_⟩
      intro b' u' hs' hr'
      by_cases hbb : b' = b
      · subst hbb
        rw [hs] at hs'
        exact (Finset.singleton_injective hs').symm
      · exfalso
        have := fin2_ne b b' hbb
        subst this
        exact H3 a hat (fin2_both (fun b => R a b) b hr hr')
    · rcases H2 a hat with h | h
      · obtain ⟨x, hx⟩ := Finset.card_eq_one.mp (le_antisymm h (Finset.card_pos.mpr h0))
        exact ⟨x, ⟨0, hx⟩, fun b u hs hr => absurd ⟨b, u, hs, hr⟩ hf⟩
      · obtain ⟨x, hx⟩ := Finset.card_eq_one.mp (le_antisymm h (Finset.card_pos.mpr h1))
        exact ⟨x, ⟨1, hx⟩, fun b u hs hr => absurd ⟨b, u, hs, hr⟩ hf⟩
  choose c hc1 hc2 using hex
  have hcK : ∀ (a : ℕ) (ha : a ∈ T), c ⟨a, ha⟩ ∈ T.attach.image c := fun a ha =>
    Finset.mem_image_of_mem c (Finset.mem_attach T ⟨a, ha⟩)
  refine ⟨T.attach.image c, ?_, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨a, hat, u, hu, v, hv, rfl⟩ := H5 e he
    have haT : a ∈ T := Finset.mem_filter.mpr ⟨hat, ⟨u, hu⟩, ⟨v, hv⟩⟩
    refine ⟨c ⟨a, haT⟩, hcK a haT, ?_⟩
    obtain ⟨b, hb⟩ := hc1 ⟨a, haT⟩
    rcases fin2_sub b with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h] at hb
      have hu' : u ∈ ({c ⟨a, haT⟩} : Finset (Fin n)) := hb ▸ hu
      rw [Finset.mem_singleton.mp hu']
      exact Sym2.mem_mk_left _ _
    · rw [h] at hb
      have hv' : v ∈ ({c ⟨a, haT⟩} : Finset (Fin n)) := hb ▸ hv
      rw [Finset.mem_singleton.mp hv']
      exact Sym2.mem_mk_right _ _
  · rintro u ⟨a, hat, b, hs, hr⟩
    have haT := hA a hat b u hs hr
    rw [hc2 ⟨a, haT⟩ b u hs hr]
    exact hcK a haT
  · rintro w ⟨a, hat, b, h2, hr, hs⟩
    have haT : a ∈ T := memT a hat b (Finset.card_pos.mp (by omega))
      (by rw [hs]; exact Finset.singleton_nonempty w)
    obtain ⟨b', hb'⟩ := hc1 ⟨a, haT⟩
    have hbb : b' ≠ b := by
      rintro rfl
      rw [hb', Finset.card_singleton] at h2
      omega
    rw [fin2_ne b b' hbb, hs] at hb'
    rw [Finset.singleton_injective hb']
    exact hcK a haT
  · intro P hP
    have hcount := count_fibres T.attach c P ?_
    · rw [Finset.card_attach] at hcount
      exact le_trans hcount (Finset.card_le_card hTsub)
    intro u hu
    obtain ⟨⟨a, hat, b, hs, hr⟩, v, hadj, hU, hvW, hvK⟩ := hP u hu
    have haT := hA a hat b u hs hr
    obtain ⟨a', hat', u', hu', v', hv', heq⟩ := H5 _ (H6 u v hadj hU)
    have haT' : a' ∈ T := Finset.mem_filter.mpr ⟨hat', ⟨u', hu'⟩, ⟨v', hv'⟩⟩
    have hc0 : ∃ c0 : Fin 2, u ∈ side a' c0 ∧ v ∈ side a' (1 - c0) := by
      rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨0, hu', hv'⟩
      · exact ⟨1, hv', hu'⟩
    obtain ⟨c0, hu0, hv0⟩ := hc0
    have hne : a ≠ a' := by
      rintro rfl
      by_cases hcb : c0 = b
      · subst hcb
        exact hvW (H7 a hat c0 u hs hr hv0)
      · rw [fin2_ne' b c0 hcb, hs] at hv0
        rw [Finset.mem_singleton.mp hv0] at hadj
        exact G.irrefl hadj
    refine ⟨⟨a, haT⟩, Finset.mem_attach _ _, ⟨a', haT'⟩, Finset.mem_attach _ _,
      fun h => hne (congrArg Subtype.val h), (hc2 ⟨a, haT⟩ b u hs hr).symm, ?_⟩
    obtain ⟨b'', hb''⟩ := hc1 ⟨a', haT'⟩
    by_cases hcb : b'' = c0
    · subst hcb
      rw [hb''] at hu0
      exact (Finset.mem_singleton.mp hu0).symm
    · exfalso
      rw [fin2_ne c0 b'' hcb] at hb''
      rw [hb''] at hv0
      rw [Finset.mem_singleton.mp hv0] at hvK
      exact hvK (hcK a' haT')
def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl
lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega
lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]
def W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false
lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]
lemma W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, foldl_stepWire_length, hpre_len]
  have hCj : W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + k) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append]
    exact (foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact getD_ge_length w0 i (by omega)
lemma W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    W n C x u = x ⟨u, hu⟩ := by
  simp only [W]
  rw [wires_eq_foldl, foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]
lemma W_or (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (a b : ℕ) (hin : (gateAt C k).inputs = [a, b])
    (ha : a < n + k) (hb : b < n + k) :
    W n C x (n + k) = (W n C x a || W n C x b) := by
  rw [W_gate n C x k hk, hop, hin]
  simp [GateOp.eval, ha, hb]
lemma W_and (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.and) (a b : ℕ) (hin : (gateAt C k).inputs = [a, b])
    (ha : a < n + k) (hb : b < n + k) :
    W n C x (n + k) = (W n C x a && W n C x b) := by
  rw [W_gate n C x k hk, hop, hin]
  simp [GateOp.eval, ha, hb]
def AO (n : ℕ) (C : Circuit) : Prop :=
  ∀ k < C.gates.length, ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) ∧
    ∃ a b, (gateAt C k).inputs = [a, b] ∧ a < n + k ∧ b < n + k
open PEqualNP.EdgeOwnership in
lemma coneFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega
open PEqualNP.EdgeOwnership in
lemma coneStep_getD_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    (coneStep n cs g).getD cs.length [] =
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) []) := by
  simp [coneStep, List.getD_eq_getElem?_getD]
open PEqualNP.EdgeOwnership in
lemma coneStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (coneStep n cs g).getD m [] = cs.getD m [] := by
  simp [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]
open PEqualNP.EdgeOwnership in
lemma coneFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (coneStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (coneStep n cs g) (by simp [coneStep]; omega)]
    exact coneStep_getD_lt n cs g k hk
open PEqualNP.EdgeOwnership in
lemma inCone_iff (n : ℕ) (C : Circuit) (i k : ℕ) (hk : k < C.gates.length) :
    InCone n C i k ↔ ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
      (i = w - n ∨ InCone n C i (w - n)) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : cones n C = post.foldl (coneStep n) (coneStep n (pre.foldl (coneStep n) []) gk) := by
    simp only [cones]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (coneStep n) []).length = k := by
    rw [coneFold_length]; simp [hpre_len]
  have hl1 : (coneStep n (pre.foldl (coneStep n) []) gk).length = k + 1 := by
    simp [coneStep, hl0]
  have h1 : (cones n C).getD k [] =
      (gk.inputs.filter (fun w => decide (n ≤ w ∧ w < n + k))).flatMap
        (fun w => (w - n) :: (pre.foldl (coneStep n) []).getD (w - n) []) := by
    rw [hc, coneFold_getD_lt n post _ k (by omega)]
    have h := coneStep_getD_last n (pre.foldl (coneStep n) []) gk
    rw [hl0] at h
    exact h
  have h2 : ∀ m, m < k → (cones n C).getD m [] = (pre.foldl (coneStep n) []).getD m [] := by
    intro m hm
    rw [hc, coneFold_getD_lt n post _ m (by omega)]
    exact coneStep_getD_lt n _ gk m (by omega)
  unfold InCone
  rw [h1]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw, hn, hlt⟩, h⟩
    refine ⟨w, hw, hn, hlt, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [h2 (w - n) (by omega)]
      exact h
  · rintro ⟨w, hw, hn, hlt, h⟩
    refine ⟨w, ⟨hw, hn, hlt⟩, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [← h2 (w - n) (by omega)]
      exact h
open PEqualNP.EdgeOwnership in
lemma inCone_c1 (n : ℕ) (C : Circuit) (hA : AO n C) (i k : ℕ) (hk : k < C.gates.length)
    (hm : n + i ∈ (gateAt C k).inputs) : InCone n C i k := by
  rw [inCone_iff n C i k hk]
  have hlt : n + i < n + k := by
    obtain ⟨_, a, b, hin, ha, hb⟩ := hA k hk
    rw [hin] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    omega
  exact ⟨n + i, hm, by omega, hlt, Or.inl (by omega)⟩
open PEqualNP.EdgeOwnership in
lemma inCone_c2 (n : ℕ) (C : Circuit) (hA : AO n C) (t i k : ℕ) (hk : k < C.gates.length)
    (hc : InCone n C t i) (hm : n + i ∈ (gateAt C k).inputs) : InCone n C t k := by
  rw [inCone_iff n C t k hk]
  have hlt : n + i < n + k := by
    obtain ⟨_, a, b, hin, ha, hb⟩ := hA k hk
    rw [hin] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    omega
  have he : n + i - n = i := by omega
  exact ⟨n + i, hm, by omega, hlt, Or.inr (by rw [he]; exact hc)⟩
def OrStep (n : ℕ) (C : Circuit) (u v : ℕ) : Prop :=
  ∃ k, u = n + k ∧ k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧ v ∈ (gateAt C k).inputs
def OrR (n : ℕ) (C : Circuit) : ℕ → ℕ → Prop := Relation.ReflTransGen (OrStep n C)
def Leaf (n : ℕ) (C : Circuit) (v : ℕ) : Prop :=
  v < n ∨ ∃ h, v = n + h ∧ h < C.gates.length ∧ (gateAt C h).op = GateOp.and
lemma orStep_lt (n : ℕ) (C : Circuit) (hA : AO n C) (u v : ℕ) (h : OrStep n C u v) : v < u := by
  obtain ⟨k, rfl, hk, _, hv⟩ := h
  obtain ⟨_, a, b, hin, ha, hb⟩ := hA k hk
  rw [hin] at hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  omega
lemma orR_le (n : ℕ) (C : Circuit) (hA : AO n C) (u v : ℕ) (h : OrR n C u v) : v ≤ u := by
  induction h with
  | refl => exact le_rfl
  | tail _ h2 ih => have := orStep_lt n C hA _ _ h2; omega
lemma orStep_mono (n : ℕ) (C : Circuit) (hA : AO n C) (x : Fin n → Bool) (u v : ℕ)
    (h : OrStep n C u v) (hv : W n C x v = true) : W n C x u = true := by
  obtain ⟨k, rfl, hk, hop, hin⟩ := h
  obtain ⟨_, a, b, hab, ha, hb⟩ := hA k hk
  rw [W_or n C x k hk hop a b hab ha hb]
  rw [hab] at hin
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
  rcases hin with rfl | rfl
  · simp [hv]
  · simp [hv]
lemma orR_mono (n : ℕ) (C : Circuit) (hA : AO n C) (x : Fin n → Bool) (u v : ℕ)
    (h : OrR n C u v) (hv : W n C x v = true) : W n C x u = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head h1 _ ih => exact orStep_mono n C hA x _ _ h1 ih
lemma orR_leaf_true (n : ℕ) (C : Circuit) (hA : AO n C) (x : Fin n → Bool) :
    ∀ u, u < n + C.gates.length → W n C x u = true →
      ∃ v, OrR n C u v ∧ Leaf n C v ∧ W n C x v = true := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu hx
    by_cases h1 : u < n
    · exact ⟨u, Relation.ReflTransGen.refl, Or.inl h1, hx⟩
    · obtain ⟨k, rfl⟩ : ∃ k, u = n + k := ⟨u - n, by omega⟩
      have hk : k < C.gates.length := by omega
      obtain ⟨hop, a, b, hab, ha, hb⟩ := hA k hk
      rcases hop with hop | hop
      · exact ⟨n + k, Relation.ReflTransGen.refl, Or.inr ⟨k, rfl, hk, hop⟩, hx⟩
      · rw [W_or n C x k hk hop a b hab ha hb] at hx
        simp only [Bool.or_eq_true] at hx
        rcases hx with hx | hx
        · obtain ⟨v, hv1, hv2, hv3⟩ := ih a ha (by omega) hx
          exact ⟨v, Relation.ReflTransGen.head ⟨k, rfl, hk, hop, by rw [hab]; simp⟩ hv1, hv2, hv3⟩
        · obtain ⟨v, hv1, hv2, hv3⟩ := ih b hb (by omega) hx
          exact ⟨v, Relation.ReflTransGen.head ⟨k, rfl, hk, hop, by rw [hab]; simp⟩ hv1, hv2, hv3⟩
lemma orR_leaf (n : ℕ) (C : Circuit) (hA : AO n C) :
    ∀ u, u < n + C.gates.length → ∃ v, OrR n C u v ∧ Leaf n C v := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu
    by_cases h1 : u < n
    · exact ⟨u, Relation.ReflTransGen.refl, Or.inl h1⟩
    · obtain ⟨k, rfl⟩ : ∃ k, u = n + k := ⟨u - n, by omega⟩
      have hk : k < C.gates.length := by omega
      obtain ⟨hop, a, b, hab, ha, hb⟩ := hA k hk
      rcases hop with hop | hop
      · exact ⟨n + k, Relation.ReflTransGen.refl, Or.inr ⟨k, rfl, hk, hop⟩⟩
      · obtain ⟨v, hv1, hv2⟩ := ih a ha (by omega)
        exact ⟨v, Relation.ReflTransGen.head ⟨k, rfl, hk, hop, by rw [hab]; simp⟩ hv1, hv2⟩
open PEqualNP.EdgeOwnership in
lemma orR_cone (n : ℕ) (C : Circuit) (hA : AO n C) (h u : ℕ) (hr : OrR n C u (n + h)) :
    ∀ k, u = n + k → k < C.gates.length → h = k ∨ InCone n C h k := by
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl => intro k hk _; left; omega
  | head h1 h2 ih =>
    rename_i u c
    intro k hk hlen
    have hle := orR_le n C hA _ _ h2
    have hlt := orStep_lt n C hA _ _ h1
    obtain ⟨k', hk', _, _, hin⟩ := h1
    have hkk : k' = k := by omega
    subst hkk
    have hc : c = n + (c - n) := by omega
    rcases ih (c - n) hc (by omega) with h3 | h3
    · right
      refine inCone_c1 n C hA h k' hlen ?_
      rw [h3, ← hc]
      exact hin
    · right
      refine inCone_c2 n C hA h (c - n) k' hlen h3 ?_
      rw [← hc]
      exact hin
lemma biclique_star {n : ℕ} (G : SimpleGraph (Fin n))
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (A B : Finset (Fin n)) (hab : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) :
    A.card ≤ 1 ∨ B.card ≤ 1 := by
  by_contra hcon
  simp only [not_or, not_le] at hcon
  obtain ⟨a, ha, c, hc, hac⟩ := Finset.one_lt_card.mp hcon.1
  obtain ⟨b, hb, d, hd, hbd⟩ := Finset.one_lt_card.mp hcon.2
  exact h4 a b c d hac hbd
    ⟨hab a ha b hb, (hab c hc b hb).symm, hab c hc d hd, (hab a ha d hd).symm⟩
lemma opnd_lt (n : ℕ) (C : Circuit) (hA : AO n C) (a : ℕ) (ha : a < C.gates.length)
    (o : Fin 2 → ℕ) (hin : (gateAt C a).inputs = [o 0, o 1]) : ∀ b : Fin 2, o b < n + a := by
  obtain ⟨_, a1, b1, hab, ha1, hb1⟩ := hA a ha
  rw [hin] at hab
  simp only [List.cons.injEq, and_true] at hab
  intro b
  rcases fin2_sub b with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> omega
lemma top_true (n : ℕ) (C : Circuit) (hA : AO n C) (a : ℕ) (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and)
    (o : Fin 2 → ℕ) (hin : (gateAt C a).inputs = [o 0, o 1]) (x : Fin n → Bool)
    (h : ∀ b : Fin 2, W n C x (o b) = true) : W n C x (n + a) = true := by
  have hlt := opnd_lt n C hA a ha o hin
  rw [W_and n C x a ha hop (o 0) (o 1) hin (hlt 0) (hlt 1), h 0, h 1]
  rfl
lemma sem_both (n : ℕ) (C : Circuit) (hA : AO n C) (a : ℕ) (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and)
    (o : Fin 2 → ℕ) (hin : (gateAt C a).inputs = [o 0, o 1]) (g : ℕ)
    (h0 : OrR n C (o 0) (n + g)) (h1 : OrR n C (o 1) (n + g)) (x : Fin n → Bool)
    (hx : W n C x (n + g) = true) : W n C x (n + a) = true := by
  apply top_true n C hA a ha hop o hin x
  intro b
  rcases fin2_sub b with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
  · exact orR_mono n C hA x _ _ h0 hx
  · exact orR_mono n C hA x _ _ h1 hx
lemma sem_mixed (n : ℕ) (C : Circuit) (hA : AO n C) (a : ℕ) (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and)
    (o : Fin 2 → ℕ) (hin : (gateAt C a).inputs = [o 0, o 1]) (g : ℕ) (b : Fin 2) (w : Fin n)
    (hb : OrR n C (o b) (n + g)) (hw : OrR n C (o (1 - b)) w.val) (x : Fin n → Bool)
    (hx : W n C x (n + g) = true) (hxw : x w = true) : W n C x (n + a) = true := by
  have hww : W n C x w.val = true := by
    rw [W_input n C x w.val w.isLt]; exact hxw
  apply top_true n C hA a ha hop o hin x
  intro b'
  by_cases hbb : b' = b
  · rw [hbb]; exact orR_mono n C hA x _ _ hb hx
  · rw [fin2_ne b b' hbb]; exact orR_mono n C hA x _ _ hw hww
open PEqualNP.EdgeOwnership in
lemma sem_adj (n : ℕ) (C : Circuit) (hA : AO n C) (a : ℕ) (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and)
    (o : Fin 2 → ℕ) (hin : (gateAt C a).inputs = [o 0, o 1]) (u v : Fin n)
    (hu : OrR n C (o 0) u.val) (hv : OrR n C (o 1) v.val) :
    W n C (pairInput u v) (n + a) = true := by
  apply top_true n C hA a ha hop o hin
  intro b
  rcases fin2_sub b with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
  · refine orR_mono n C hA _ _ _ hu ?_
    rw [W_input n C _ u.val u.isLt]; simp [pairInput]
  · refine orR_mono n C hA _ _ _ hv ?_
    rw [W_input n C _ v.val v.isLt]; simp [pairInput]
open PEqualNP.EdgeOwnership in
lemma opnd_leaf (n : ℕ) (C : Circuit) (hA : AO n C) (a : ℕ) (ha : a < C.gates.length)
    (o : Fin 2 → ℕ) (hin : (gateAt C a).inputs = [o 0, o 1]) (b : Fin 2) :
    (∃ w : Fin n, OrR n C (o b) w.val) ∨
      ∃ h, h < C.gates.length ∧ (gateAt C h).op = GateOp.and ∧ OrR n C (o b) (n + h) ∧
        InCone n C h a := by
  have hlt := opnd_lt n C hA a ha o hin b
  obtain ⟨v, hv1, hv2⟩ := orR_leaf n C hA (o b) (by omega)
  rcases hv2 with hv | ⟨h, rfl, hh, hhop⟩
  · exact Or.inl ⟨⟨v, hv⟩, hv1⟩
  · right
    refine ⟨h, hh, hhop, hv1, ?_⟩
    have hle := orR_le n C hA _ _ hv1
    have hu' : o b = n + (o b - n) := by omega
    have hmem : o b ∈ (gateAt C a).inputs := by
      rw [hin]
      rcases fin2_sub b with ⟨h', -⟩ | ⟨h', -⟩ <;> rw [h'] <;> simp
    rcases orR_cone n C hA h (o b) hv1 (o b - n) hu' (by omega) with h3 | h3
    · refine inCone_c1 n C hA h a ha ?_
      rw [h3, ← hu']; exact hmem
    · refine inCone_c2 n C hA h (o b - n) a ha h3 ?_
      rw [← hu']; exact hmem
open PEqualNP.EdgeOwnership in
open PEqualNP.EdgeOwnership in
lemma pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
  simp [pairInput]
open PEqualNP.EdgeOwnership in
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
theorem main_abs (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hA : AO n C)
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (tops centreless : Finset ℕ) (g : ℕ)
    (htops : ∀ a ∈ tops, a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧
      ∀ x : Fin n → Bool, W n C x (n + a) = true → graphFun G ∅ x = true)
    (hg : ¬ ∀ x : Fin n → Bool, W n C x (n + g) = true → graphFun G ∅ x = true)
    (hleaf : ∀ a ∈ tops, ∀ h, h < C.gates.length → (gateAt C h).op = GateOp.and →
      PEqualNP.EdgeOwnership.InCone n C h a → h = g)
    (o : ℕ → Fin 2 → ℕ) (hin : ∀ a ∈ tops, (gateAt C a).inputs = [o a 0, o a 1])
    (side : ℕ → Fin 2 → Finset (Fin n))
    (hside : ∀ a ∈ tops, ∀ (b : Fin 2) (u : Fin n), u ∈ side a b ↔ OrR n C (o a b) u.val)
    (R : ℕ → Fin 2 → Prop)
    (hR : ∀ a ∈ tops, ∀ b : Fin 2, R a b ↔ OrR n C (o a b) (n + g))
    (Wm : Finset (Fin n))
    (hW : ∀ w : Fin n, (∀ x : Fin n → Bool, W n C x (n + g) = true → x w = true →
      graphFun G ∅ x = true) → w ∈ Wm)
    (starEdges Ustar : Finset (Sym2 (Fin n)))
    (H1 : ∀ a ∈ tops, a ∈ centreless → (side a 0 = ∅ ∨ side a 1 = ∅))
    (H5 : ∀ e ∈ starEdges, ∃ a ∈ tops, ∃ u ∈ side a 0, ∃ v ∈ side a 1, e = s(u, v))
    (H6 : ∀ u v, G.Adj u v → s(u, v) ∉ Ustar → s(u, v) ∈ starEdges) :
    ∃ K : Finset (Fin n), (∀ e ∈ starEdges, ∃ v ∈ K, v ∈ e) ∧
      (∀ u, (∃ a ∈ tops, ∃ b : Fin 2, side a b = {u} ∧ R a b) → u ∈ K) ∧
      (∀ w, (∃ a ∈ tops, ∃ b : Fin 2, 2 ≤ (side a b).card ∧ R a b ∧ side a (1 - b) = {w}) →
        w ∈ K) ∧
      ∀ P : Finset (Fin n), (∀ u ∈ P, (∃ a ∈ tops, ∃ b : Fin 2, side a b = {u} ∧ R a b) ∧
          ∃ v, G.Adj u v ∧ s(u, v) ∉ Ustar ∧ v ∉ Wm ∧ v ∉ K) →
        K.card + P.card ≤ (tops \ centreless).card := by
  refine core G tops centreless side R Wm starEdges Ustar H1 ?_ ?_ ?_ H5 H6 ?_
  · intro a hat
    obtain ⟨ha, hop, hbel⟩ := htops a hat
    refine biclique_star G h4 (side a 0) (side a 1) ?_
    intro u hu v hv
    rw [← graphFun_pair G u v]
    exact hbel _ (sem_adj n C hA a ha hop (o a) (hin a hat) u v
      ((hside a hat 0 u).mp hu) ((hside a hat 1 v).mp hv))
  · rintro a hat ⟨h0, h1⟩
    obtain ⟨ha, hop, hbel⟩ := htops a hat
    apply hg
    intro x hx
    exact hbel x (sem_both n C hA a ha hop (o a) (hin a hat) g
      ((hR a hat 0).mp h0) ((hR a hat 1).mp h1) x hx)
  · intro a hat b he
    obtain ⟨ha, hop, hbel⟩ := htops a hat
    rcases opnd_leaf n C hA a ha (o a) (hin a hat) b with ⟨w, hw⟩ | ⟨h, hh, hhop, hr, hc⟩
    · have : w ∈ side a b := (hside a hat b w).mpr hw
      rw [he] at this
      exact absurd this (Finset.notMem_empty w)
    · rw [hleaf a hat h hh hhop hc] at hr
      exact (hR a hat b).mpr hr
  · intro a hat b u _ hr w hw
    obtain ⟨ha, hop, hbel⟩ := htops a hat
    apply hW
    intro x hx hxw
    exact hbel x (sem_mixed n C hA a ha hop (o a) (hin a hat) g b w
      ((hR a hat b).mp hr) ((hside a hat (1 - b) w).mp hw) x hx hxw)
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
lemma mem_filter' {α : Type*} (p : α → Prop) (inst : DecidablePred p) (s : Finset α) (a : α) :
    a ∈ @Finset.filter α p inst s ↔ a ∈ s ∧ p a := Finset.mem_filter
lemma orFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega
lemma orStep_mem_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) (x : ℕ) :
    x ∈ (orStep n cs g).getD cs.length [] ↔ x = cs.length ∨ (g.op = GateOp.or ∧
      ∃ w, (w ∈ g.inputs ∧ n ≤ w ∧ w < n + cs.length) ∧ x ∈ cs.getD (w - n) []) := by
  by_cases hop : g.op = GateOp.or
  · simp [orStep, List.getD_eq_getElem?_getD, hop]
  · simp [orStep, List.getD_eq_getElem?_getD, hop]
lemma orStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (orStep n cs g).getD m [] = cs.getD m [] := by
  simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]
lemma orFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (orStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (orStep n cs g) (by simp [orStep]; omega)]
    exact orStep_getD_lt n cs g k hk
lemma orReaches_iff (n : ℕ) (C : Circuit) (g k : ℕ) (hk : k < C.gates.length) :
    OrReaches n C (n + k) g ↔ g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ OrReaches n C w g) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : orSets n C = post.foldl (orStep n) (orStep n (pre.foldl (orStep n) []) gk) := by
    simp only [orSets]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (orStep n) []).length = k := by
    rw [orFold_length]; simp [hpre_len]
  have hl1 : (orStep n (pre.foldl (orStep n) []) gk).length = k + 1 := by
    simp [orStep, hl0]
  have h1 : ∀ x, x ∈ (orSets n C).getD k [] ↔ x = k ∨ (gk.op = GateOp.or ∧
      ∃ w, (w ∈ gk.inputs ∧ n ≤ w ∧ w < n + k) ∧
        x ∈ (pre.foldl (orStep n) []).getD (w - n) []) := by
    intro x
    rw [hc, orFold_getD_lt n post _ k (by omega)]
    have h := orStep_mem_last n (pre.foldl (orStep n) []) gk x
    rw [hl0] at h
    exact h
  have h2 : ∀ m, m < k → (orSets n C).getD m [] = (pre.foldl (orStep n) []).getD m [] := by
    intro m hm
    rw [hc, orFold_getD_lt n post _ m (by omega)]
    exact orStep_getD_lt n _ gk m (by omega)
  have e : n + k - n = k := by omega
  unfold OrReaches
  rw [e, h1 g]
  constructor
  · rintro ⟨_, h | ⟨hop, w, ⟨hw, hn, hlt⟩, h⟩⟩
    · exact Or.inl h
    · right
      refine ⟨hop, w, hw, hn, hlt, hn, ?_⟩
      rw [h2 (w - n) (by omega)]
      exact h
  · rintro (h | ⟨hop, w, hw, hn, hlt, _, h⟩)
    · exact ⟨by omega, Or.inl h⟩
    · refine ⟨by omega, Or.inr ⟨hop, w, ⟨hw, hn, hlt⟩, ?_⟩⟩
      rw [← h2 (w - n) (by omega)]
      exact h
lemma orReaches_orR (n : ℕ) (C : Circuit) :
    ∀ w, w < n + C.gates.length → ∀ g, OrReaches n C w g → OrR n C w (n + g) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw g hr
    have hn : n ≤ w := hr.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : k < C.gates.length := by omega
    rcases (orReaches_iff n C g k hk).mp hr with h | ⟨hop, c, hc, hcn, hclt, hcr⟩
    · rw [h]
      exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.head ⟨k, rfl, hk, hop, hc⟩ (ih c hclt (by omega) g hcr)
lemma orR_orReaches (n : ℕ) (C : Circuit) (hA : AO n C) (g : ℕ) (hg : g < C.gates.length) :
    ∀ w, w < n + C.gates.length → OrR n C w (n + g) → OrReaches n C w g := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hr
    rcases Relation.ReflTransGen.cases_head hr with h | ⟨c, ⟨k, hk1, hk, hop, hc⟩, hcr⟩
    · rw [h]
      exact (orReaches_iff n C g g hg).mpr (Or.inl rfl)
    · subst hk1
      have hle := orR_le n C hA _ _ hcr
      have hclt : c < n + k := by
        obtain ⟨_, a, b, hab, ha, hb⟩ := hA k hk
        rw [hab] at hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        omega
      exact (orReaches_iff n C g k hk).mpr
        (Or.inr ⟨hop, c, hc, by omega, hclt, ih c hclt (by omega) hcr⟩)
lemma mem_orIn (n : ℕ) (C : Circuit) (hA : AO n C) (w : ℕ) (hw : w < n + C.gates.length)
    (u : Fin n) : u ∈ orIn n C w ↔ OrR n C w u.val := by
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (h | ⟨k, hk, hr, hop, hu⟩)
    · rw [h]
      exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.tail (orReaches_orR n C w hw k hr) ⟨k, rfl, hk, hop, hu⟩
  · intro h
    rcases Relation.ReflTransGen.cases_tail h with h1 | ⟨c, hc, ⟨k, rfl, hk, hop, hu⟩⟩
    · left
      exact h1
    · right
      exact ⟨k, hk, orR_orReaches n C hA k hk w hw hc, hop, hu⟩
lemma ao_of (n : ℕ) (C : Circuit) (h : IsAO2 n C) : AO n C := by
  obtain ⟨hao, hrb, hlen⟩ := h
  intro k hk
  have hmem : gateAt C k ∈ C.gates := by
    rw [gateAt_eq C k hk]
    exact List.getElem_mem hk
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (hlen _ hmem)
  exact ⟨hao _ hmem, a, b, hab, hrb k hk a (by rw [hab]; simp), hrb k hk b (by rw [hab]; simp)⟩
lemma opnd_eq (n : ℕ) (C : Circuit) (hA : AO n C) (a : ℕ) (ha : a < C.gates.length) :
    (gateAt C a).inputs = [opnd C a 0, opnd C a 1] := by
  obtain ⟨_, p, q, hpq, _, _⟩ := hA a ha
  simp [opnd, hpq]
lemma nfc (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (h : NoFourCycle G) :
    ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) := by
  rintro a b c d hac hbd ⟨h1, h2, h3, h4⟩
  have h0 := h a c hac
  have h5 : 1 < (Finset.univ.filter fun w => G.Adj a w ∧ G.Adj c w).card :=
    Finset.one_lt_card.mpr ⟨b, by simp [h1, h2.symm], d, by simp [h4.symm, h3], hbd⟩
  omega
theorem final : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
  PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C →
  PEqualNP.TopForm.TopForm G C → ∀ (g : ℕ), PEqualNP.TopForm.junk G C = {g} →
    ∃ K : Finset (Fin n), (∀ e ∈ PEqualNP.TopForm.starEdges G C, ∃ v ∈ K, v ∈ e) ∧
      (Finset.univ : Finset (Fin n)).filter (fun u => ∃ a ∈ PEqualNP.TopForm.tops G C, ∃ b : Fin 2,
          PEqualNP.TopForm.side (n := n) C a b = {u} ∧
          PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C a b) g) ⊆ K ∧
      (Finset.univ : Finset (Fin n)).filter (fun w => ∃ a ∈ PEqualNP.TopForm.tops G C, ∃ b : Fin 2,
          2 ≤ (PEqualNP.TopForm.side (n := n) C a b).card ∧
          PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C a b) g ∧
          PEqualNP.TopForm.side (n := n) C a (1 - b) = {w}) ⊆ K ∧
      K.card + ((Finset.univ : Finset (Fin n)).filter (fun u => (∃ a ∈ PEqualNP.TopForm.tops G C, ∃ b : Fin 2,
          PEqualNP.TopForm.side (n := n) C a b = {u} ∧
          PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C a b) g) ∧
          ∃ v, G.Adj u v ∧ s(u, v) ∉ PEqualNP.TopForm.Ustar G C ∧ v ∉ PEqualNP.TopForm.wmax G C g ∧ v ∉ K)).card ≤
        (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card := by
  intro n G _ C hNF _ hL hTF g hjunk
  have hA : AO n C := ao_of n C hL.1
  have hgj : g ∈ junk G C := by rw [hjunk]; exact Finset.mem_singleton_self g
  obtain ⟨-, hgop, hglen, xg, hxg1, hxg2⟩ := (mem_filter' _ _ _ _).mp hgj
  have htops : ∀ a ∈ tops G C, a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧
      ∀ x : Fin n → Bool, W n C x (n + a) = true → graphFun G ∅ x = true := by
    intro a ha
    have ha0 := (mem_filter' _ _ _ _).mp ha
    exact ⟨Finset.mem_range.mp ha0.1, ha0.2.1, ha0.2.2⟩
  have hleaf : ∀ a ∈ tops G C, ∀ h, h < C.gates.length → (gateAt C h).op = GateOp.and →
      InCone n C h a → h = g := by
    intro a ha h hh hhop hc
    obtain ⟨ha1, ha2, _⟩ := htops a ha
    by_contra hne
    have hbel : BelowF G C h := by
      intro x hx
      by_contra hf
      have hd : IsDirtyAnd n G C h := by
        unfold IsDirtyAnd IsDirty
        exact ⟨hhop, hh, x, hx, Bool.eq_false_iff.mpr hf⟩
      have hj : h ∈ junk G C := (mem_filter' _ _ _ _).mpr ⟨Finset.mem_range.mpr hh, hd⟩
      rw [hjunk] at hj
      exact hne (Finset.mem_singleton.mp hj)
    exact hTF h hh a ha1 hhop hbel ha2 hc
  have hg : ¬ ∀ x : Fin n → Bool, W n C x (n + g) = true → graphFun G ∅ x = true := by
    intro h
    have h6 := h xg hxg1
    rw [hxg2] at h6
    exact Bool.false_ne_true h6
  have hin : ∀ a ∈ tops G C, (gateAt C a).inputs = [opnd C a 0, opnd C a 1] :=
    fun a ha => opnd_eq n C hA a (htops a ha).1
  have hol : ∀ a ∈ tops G C, ∀ b : Fin 2, opnd C a b < n + C.gates.length := by
    intro a ha b
    have h7 := opnd_lt n C hA a (htops a ha).1 (fun b => opnd C a b) (hin a ha) b
    have h8 := (htops a ha).1
    omega
  have hside : ∀ a ∈ tops G C, ∀ (b : Fin 2) (u : Fin n),
      u ∈ side (n := n) C a b ↔ OrR n C (opnd C a b) u.val :=
    fun a ha b u => mem_orIn n C hA _ (hol a ha b) u
  have hR : ∀ a ∈ tops G C, ∀ b : Fin 2,
      OrReaches n C (opnd C a b) g ↔ OrR n C (opnd C a b) (n + g) :=
    fun a ha b => ⟨orReaches_orR n C _ (hol a ha b) g,
      orR_orReaches n C hA g hglen _ (hol a ha b)⟩
  have hW : ∀ w : Fin n, (∀ x : Fin n → Bool, W n C x (n + g) = true → x w = true →
      graphFun G ∅ x = true) → w ∈ wmax G C g :=
    fun w h => (mem_filter' _ _ _ _).mpr ⟨Finset.mem_univ w, h⟩
  have H1 : ∀ a ∈ tops G C, a ∈ centreless G C →
      (side (n := n) C a 0 = ∅ ∨ side (n := n) C a 1 = ∅) :=
    fun a _ hc => ((mem_filter' _ _ _ _).mp hc).2
  have H5 : ∀ e ∈ starEdges G C, ∃ a ∈ tops G C, ∃ u ∈ side (n := n) C a 0,
      ∃ v ∈ side (n := n) C a 1, e = s(u, v) := by
    intro e he
    simp only [starEdges, Finset.mem_biUnion, Finset.mem_image, Finset.mem_product] at he
    obtain ⟨a, ha, p, ⟨hp1, hp2⟩, rfl⟩ := he
    exact ⟨a, ha, p.1, hp1, p.2, hp2, rfl⟩
  have H6 : ∀ u v, G.Adj u v → s(u, v) ∉ Ustar G C → s(u, v) ∈ starEdges G C := by
    intro u v hadj hU
    by_contra hns
    exact hU (Finset.mem_sdiff.mpr
      ⟨SimpleGraph.mem_edgeFinset.mpr ((SimpleGraph.mem_edgeSet G).mpr hadj), hns⟩)
  obtain ⟨K, h1, h2, h3, h5⟩ := main_abs n G C hA (nfc n G hNF) (tops G C) (centreless G C) g
    htops hg hleaf (fun a b => opnd C a b) hin (fun a b => side (n := n) C a b) hside
    (fun a b => OrReaches n C (opnd C a b) g) hR (wmax G C g) hW (starEdges G C) (Ustar G C)
    H1 H5 H6
  refine ⟨K, h1, ?_, ?_, ?_⟩
  · intro u hu
    exact h2 u ((mem_filter' _ _ _ _).mp hu).2
  · intro w hw
    exact h3 w ((mem_filter' _ _ _ _).mp hw).2
  · exact h5 _ (fun u hu => ((mem_filter' _ _ _ _).mp hu).2)
end P2
theorem prev2 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
  PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C →
  PEqualNP.TopForm.TopForm G C → ∀ (g : ℕ), PEqualNP.TopForm.junk G C = {g} →
    ∃ K : Finset (Fin n), (∀ e ∈ PEqualNP.TopForm.starEdges G C, ∃ v ∈ K, v ∈ e) ∧
      (Finset.univ : Finset (Fin n)).filter (fun u => ∃ a ∈ PEqualNP.TopForm.tops G C, ∃ b : Fin 2,
          PEqualNP.TopForm.side (n := n) C a b = {u} ∧
          PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C a b) g) ⊆ K ∧
      (Finset.univ : Finset (Fin n)).filter (fun w => ∃ a ∈ PEqualNP.TopForm.tops G C, ∃ b : Fin 2,
          2 ≤ (PEqualNP.TopForm.side (n := n) C a b).card ∧
          PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C a b) g ∧
          PEqualNP.TopForm.side (n := n) C a (1 - b) = {w}) ⊆ K ∧
      K.card + ((Finset.univ : Finset (Fin n)).filter (fun u => (∃ a ∈ PEqualNP.TopForm.tops G C, ∃ b : Fin 2,
          PEqualNP.TopForm.side (n := n) C a b = {u} ∧
          PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C a b) g) ∧
          ∃ v, G.Adj u v ∧ s(u, v) ∉ PEqualNP.TopForm.Ustar G C ∧ v ∉ PEqualNP.TopForm.wmax G C g ∧ v ∉ K)).card ≤
        (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card := by
  exact PEqualNP.Outside.L_meta_2448_aux.foundation.M1528.P2.final
end M1528
theorem thm_1528 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
  PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C →
  PEqualNP.TopForm.TopForm G C → ∀ (g : ℕ), PEqualNP.TopForm.junk G C = {g} →
    ∃ K : Finset (Fin n), (∀ e ∈ PEqualNP.TopForm.starEdges G C, ∃ v ∈ K, v ∈ e) ∧
      PEqualNP.TopForm.formU G C g ⊆ K ∧ PEqualNP.TopForm.formZ G C g ⊆ K ∧
      G.edgeFinset.card + K.card + (PEqualNP.TopForm.pen G C g K).card + 1 +
        (PEqualNP.TopForm.mixing G C).card + 2 * (PEqualNP.TopForm.centreless G C).card +
        (PEqualNP.TopForm.coneGates G C g).card ≤
      C.size + (PEqualNP.TopForm.Ustar G C).card + 1 := by
  intro n G _ C h4 hE hL hT g hg
  obtain ⟨K, hcov, hU, hZ, hK⟩ := PEqualNP.Outside.L_meta_2448_aux.foundation.M1528.prev2 n G C h4 hE hL hT g hg
  have h1 := (PEqualNP.Outside.L_meta_2448_aux.foundation.M1528.prev1 n G C h4 hE hL hT).1
  have hsub1 : PEqualNP.TopForm.mixing G C ⊆ PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C := by
    intro m hm
    simp only [PEqualNP.TopForm.mixing, Finset.mem_filter] at hm
    refine Finset.mem_sdiff.mpr ⟨hm.1, fun hl => ?_⟩
    simp only [PEqualNP.TopForm.lam, Finset.mem_filter] at hl
    apply hm.2
    rw [Finset.nonempty_iff_ne_empty, Finset.nonempty_iff_ne_empty] at hl
    simp only [hl.2.1, hl.2.2.1]
  have hsub2 : PEqualNP.TopForm.coneGates G C g ⊆
      (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C) \ PEqualNP.TopForm.mixing G C :=
    Finset.filter_subset _ _
  have hc2 := Finset.card_le_card hsub2
  have hc3 := Finset.card_sdiff_add_card_eq_card hsub1
  have hj : (PEqualNP.TopForm.junk G C).card = 1 := by rw [hg]; rfl
  have hpen : (PEqualNP.TopForm.pen G C g K).card ≤
      ((Finset.univ : Finset (Fin n)).filter (fun u => (∃ a ∈ PEqualNP.TopForm.tops G C, ∃ b : Fin 2,
          PEqualNP.TopForm.side (n := n) C a b = {u} ∧
          PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C a b) g) ∧
          ∃ v, G.Adj u v ∧ s(u, v) ∉ PEqualNP.TopForm.Ustar G C ∧ v ∉ PEqualNP.TopForm.wmax G C g ∧ v ∉ K)).card := by
    apply Finset.card_le_card
    intro u hu
    simp only [PEqualNP.TopForm.pen, PEqualNP.TopForm.formU, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    exact hu
  refine ⟨K, hcov, ?_, ?_, ?_⟩
  · intro u hu
    apply hU
    simpa only [PEqualNP.TopForm.formU] using hu
  · intro w hw
    apply hZ
    simpa only [PEqualNP.TopForm.formZ] using hw
  · omega

namespace M1503
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open M1528.P1.S98
def OrStep (n : ℕ) (C : Circuit) (u v : ℕ) : Prop :=
  ∃ k, u = n + k ∧ k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧ v ∈ (gateAt C k).inputs
def OrR (n : ℕ) (C : Circuit) : ℕ → ℕ → Prop := Relation.ReflTransGen (OrStep n C)
def Leaf (n : ℕ) (C : Circuit) (v : ℕ) : Prop :=
  v < n ∨ ∃ h, v = n + h ∧ h < C.gates.length ∧ (gateAt C h).op = GateOp.and
lemma orStep_lt (n : ℕ) (C : Circuit) (hA : AO n C) (u v : ℕ) (h : OrStep n C u v) : v < u := by
  obtain ⟨k, rfl, hk, _, hv⟩ := h
  obtain ⟨_, a, b, hin, ha, hb⟩ := hA k hk
  rw [hin] at hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  omega
lemma orR_le (n : ℕ) (C : Circuit) (hA : AO n C) (u v : ℕ) (h : OrR n C u v) : v ≤ u := by
  induction h with
  | refl => exact le_rfl
  | tail _ h2 ih => have := orStep_lt n C hA _ _ h2; omega
lemma orStep_mono (n : ℕ) (C : Circuit) (hA : AO n C) (x : Fin n → Bool) (u v : ℕ)
    (h : OrStep n C u v) (hv : W n C x v = true) : W n C x u = true := by
  obtain ⟨k, rfl, hk, hop, hin⟩ := h
  obtain ⟨_, a, b, hab, ha, hb⟩ := hA k hk
  rw [W_or n C x k hk hop a b hab ha hb]
  rw [hab] at hin
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
  rcases hin with rfl | rfl
  · simp [hv]
  · simp [hv]
lemma orR_mono (n : ℕ) (C : Circuit) (hA : AO n C) (x : Fin n → Bool) (u v : ℕ)
    (h : OrR n C u v) (hv : W n C x v = true) : W n C x u = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head h1 _ ih => exact orStep_mono n C hA x _ _ h1 ih
lemma orR_leaf_true (n : ℕ) (C : Circuit) (hA : AO n C) (x : Fin n → Bool) :
    ∀ u, u < n + C.gates.length → W n C x u = true →
      ∃ v, OrR n C u v ∧ Leaf n C v ∧ W n C x v = true := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu hx
    by_cases h1 : u < n
    · exact ⟨u, Relation.ReflTransGen.refl, Or.inl h1, hx⟩
    · obtain ⟨k, rfl⟩ : ∃ k, u = n + k := ⟨u - n, by omega⟩
      have hk : k < C.gates.length := by omega
      obtain ⟨hop, a, b, hab, ha, hb⟩ := hA k hk
      rcases hop with hop | hop
      · exact ⟨n + k, Relation.ReflTransGen.refl, Or.inr ⟨k, rfl, hk, hop⟩, hx⟩
      · rw [W_or n C x k hk hop a b hab ha hb] at hx
        simp only [Bool.or_eq_true] at hx
        rcases hx with hx | hx
        · obtain ⟨v, hv1, hv2, hv3⟩ := ih a ha (by omega) hx
          exact ⟨v, Relation.ReflTransGen.head ⟨k, rfl, hk, hop, by rw [hab]; simp⟩ hv1, hv2, hv3⟩
        · obtain ⟨v, hv1, hv2, hv3⟩ := ih b hb (by omega) hx
          exact ⟨v, Relation.ReflTransGen.head ⟨k, rfl, hk, hop, by rw [hab]; simp⟩ hv1, hv2, hv3⟩
lemma orR_leaf (n : ℕ) (C : Circuit) (hA : AO n C) :
    ∀ u, u < n + C.gates.length → ∃ v, OrR n C u v ∧ Leaf n C v := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu
    by_cases h1 : u < n
    · exact ⟨u, Relation.ReflTransGen.refl, Or.inl h1⟩
    · obtain ⟨k, rfl⟩ : ∃ k, u = n + k := ⟨u - n, by omega⟩
      have hk : k < C.gates.length := by omega
      obtain ⟨hop, a, b, hab, ha, hb⟩ := hA k hk
      rcases hop with hop | hop
      · exact ⟨n + k, Relation.ReflTransGen.refl, Or.inr ⟨k, rfl, hk, hop⟩⟩
      · obtain ⟨v, hv1, hv2⟩ := ih a ha (by omega)
        exact ⟨v, Relation.ReflTransGen.head ⟨k, rfl, hk, hop, by rw [hab]; simp⟩ hv1, hv2⟩
open PEqualNP.EdgeOwnership in
lemma orR_cone (n : ℕ) (C : Circuit) (hA : AO n C) (h u : ℕ) (hr : OrR n C u (n + h)) :
    ∀ k, u = n + k → k < C.gates.length → h = k ∨ InCone n C h k := by
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl => intro k hk _; left; omega
  | head h1 h2 ih =>
    rename_i u c
    intro k hk hlen
    have hle := orR_le n C hA _ _ h2
    have hlt := orStep_lt n C hA _ _ h1
    obtain ⟨k', hk', _, _, hin⟩ := h1
    have hkk : k' = k := by omega
    subst hkk
    have hc : c = n + (c - n) := by omega
    rcases ih (c - n) hc (by omega) with h3 | h3
    · right
      refine inCone_c1 n C hA h k' hlen ?_
      rw [h3, ← hc]
      exact hin
    · right
      refine inCone_c2 n C hA h (c - n) k' hlen h3 ?_
      rw [← hc]
      exact hin
open PEqualNP.EdgeOwnership in
theorem core (n : ℕ) (C : Circuit) (hL : Least n C) (a g p q : ℕ) (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and)
    (hin : (gateAt C a).inputs = [p, q] ∨ (gateAt C a).inputs = [q, p])
    (hbel : Bel n C a)
    (hT : ∀ h, h < C.gates.length → InCone n C h a → (gateAt C h).op = GateOp.and → ¬ Bel n C h)
    (hJ : ∀ h, h < C.gates.length → (gateAt C h).op = GateOp.and → ¬ Bel n C h → h = g)
    (hg : ¬ Bel n C g)
    (hp : ∀ w, w < n → ¬ OrR n C p w) :
    p = n + g ∧ (∃ w, w < n ∧ OrR n C q w) ∧ ¬ OrR n C q (n + g) ∧
      ∀ x : Fin n → Bool, W n C x (n + a) = true ↔
        (W n C x (n + g) = true ∧ ∃ w : Fin n, OrR n C q w.val ∧ x w = true) := by
  have hA := hL.1
  obtain ⟨_, a1, b1, hab, ha1, hb1⟩ := hA a ha
  have hpq : p < n + a ∧ q < n + a := by
    rcases hin with h | h
    · rw [h] at hab
      simp only [List.cons.injEq, and_true] at hab
      omega
    · rw [h] at hab
      simp only [List.cons.injEq, and_true] at hab
      omega
  have hmem : ∀ u, u = p ∨ u = q → u ∈ (gateAt C a).inputs := by
    intro u hu
    rcases hin with h | h <;> rw [h] <;> simp <;> tauto
  have hWa : ∀ x, W n C x (n + a) = (W n C x p && W n C x q) := by
    intro x
    rcases hin with h | h
    · exact W_and n C x a ha hop p q h hpq.1 hpq.2
    · rw [W_and n C x a ha hop q p h hpq.2 hpq.1, Bool.and_comm]
  have leafg : ∀ u, u = p ∨ u = q → ∀ v, OrR n C u v → Leaf n C v → v < n ∨ v = n + g := by
    intro u hu v hr hl
    rcases hl with hl | ⟨h, rfl, hh, hhop⟩
    · exact Or.inl hl
    · right
      have hle := orR_le n C hA _ _ hr
      have hult : u < n + a := by rcases hu with rfl | rfl <;> omega
      have hu' : u = n + (u - n) := by omega
      have hc : InCone n C h a := by
        rcases orR_cone n C hA h u hr (u - n) hu' (by omega) with h3 | h3
        · refine inCone_c1 n C hA h a ha ?_
          rw [h3, ← hu']
          exact hmem u hu
        · refine inCone_c2 n C hA h (u - n) a ha h3 ?_
          rw [← hu']
          exact hmem u hu
      rw [hJ h hh hhop (hT h hh hc hhop)]
  have hpg : OrR n C p (n + g) := by
    obtain ⟨v, hv1, hv2⟩ := orR_leaf n C hA p (by omega)
    rcases leafg p (Or.inl rfl) v hv1 hv2 with h | h
    · exact absurd hv1 (hp v h)
    · rw [← h]; exact hv1
  have hWp : ∀ x, W n C x p = W n C x (n + g) := by
    intro x
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hx
      obtain ⟨v, hv1, hv2, hv3⟩ := orR_leaf_true n C hA x p (by omega) hx
      rcases leafg p (Or.inl rfl) v hv1 hv2 with h | h
      · exact absurd hv1 (hp v h)
      · rw [← h]; exact hv3
    · intro hx
      exact orR_mono n C hA x _ _ hpg hx
  have hpeq : p = n + g := by
    have hle := orR_le n C hA _ _ hpg
    by_contra hne
    have hp' : p = n + (p - n) := by omega
    obtain ⟨x, hx⟩ := least_nodup n C hL (n + g) (p - n) (by omega) (by omega)
    rw [← hp'] at hx
    exact hx (hWp x).symm
  have hqg : ¬ OrR n C q (n + g) := by
    intro hq
    apply hg
    intro x hx
    apply hbel x
    rw [hWa x, hWp x, hx, orR_mono n C hA x _ _ hq hx]
    rfl
  have hWq : ∀ x : Fin n → Bool, W n C x q = true ↔
      ∃ w : Fin n, OrR n C q w.val ∧ x w = true := by
    intro x
    constructor
    · intro hx
      obtain ⟨v, hv1, hv2, hv3⟩ := orR_leaf_true n C hA x q (by omega) hx
      rcases leafg q (Or.inr rfl) v hv1 hv2 with h | h
      · refine ⟨⟨v, h⟩, hv1, ?_⟩
        rw [← W_input n C x v h]
        exact hv3
      · rw [h] at hv1
        exact absurd hv1 hqg
    · rintro ⟨w, hw1, hw2⟩
      refine orR_mono n C hA x _ _ hw1 ?_
      rw [W_input n C x w.val w.isLt]
      exact hw2
  refine ⟨hpeq, ?_, hqg, ?_⟩
  · obtain ⟨v, hv1, hv2⟩ := orR_leaf n C hA q (by omega)
    rcases leafg q (Or.inr rfl) v hv1 hv2 with h | h
    · exact ⟨v, h, hv1⟩
    · rw [h] at hv1
      exact absurd hv1 hqg
  · intro x
    rw [hWa x, hWp x, Bool.and_eq_true, hWq x]
lemma osSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [PEqualNP.CleanedNonEdge.orStep]
    omega
lemma osStep_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (k : ℕ) (hk : k < cs.length) :
    (PEqualNP.CleanedNonEdge.orStep n cs g).getD k [] = cs.getD k [] := by
  simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left hk]
lemma osStep_gt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (k : ℕ) (hk : cs.length < k) :
    (PEqualNP.CleanedNonEdge.orStep n cs g).getD k [] = [] := by
  simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_none (by simp; omega)]
  rfl
lemma osStep_mem (n : ℕ) (cs : List (List ℕ)) (g : Gate) (i : ℕ) :
    i ∈ (PEqualNP.CleanedNonEdge.orStep n cs g).getD cs.length [] ↔
      i = cs.length ∨ (g.op = GateOp.or ∧ ∃ w ∈ g.inputs, n ≤ w ∧ w < n + cs.length ∧
        i ∈ cs.getD (w - n) []) := by
  simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (le_refl _)]
  simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some, List.mem_cons]
  by_cases hop : g.op = GateOp.or
  · rw [if_pos hop]
    simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro (h | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
      · exact Or.inl h
      · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · rintro (h | ⟨_, w, hw, h1, h2, h3⟩)
      · exact Or.inl h
      · exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
  · rw [if_neg hop]
    simp only [List.not_mem_nil, or_false]
    constructor
    · intro h; exact Or.inl h
    · rintro (h | ⟨h, _⟩)
      · exact h
      · exact absurd h hop
lemma orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).length = gs.length := by
      rw [osSets_len]; simp
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [osStep_lt n _ g j (by omega), ih i j, e1]
      constructor
      · rintro ⟨_, h3 | ⟨hop, w, hw, h1, h2, h3⟩⟩
        · exact ⟨by simp; omega, Or.inl h3⟩
        · refine ⟨by simp; omega, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
          rw [osStep_lt n _ g (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3 | ⟨hop, w, hw, h1, h2, h3⟩⟩
        · exact ⟨h, Or.inl h3⟩
        · refine ⟨h, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
          rw [osStep_lt n _ g (w - n) (by omega)] at h3
          exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have hm := osStep_mem n (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g i
      rw [hlen] at hm
      rw [hm, e1]
      constructor
      · rintro (h3 | ⟨hop, w, hw, h1, h2, h3⟩)
        · exact ⟨by simp, Or.inl h3⟩
        · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
          rw [osStep_lt n _ g (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3 | ⟨hop, w, hw, h1, h2, h3⟩⟩
        · exact Or.inl h3
        · rw [osStep_lt n _ g (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · rw [osStep_gt n _ g j (by omega)]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega
lemma orReaches_iff (n : ℕ) (C : Circuit) (j g : ℕ) :
    PEqualNP.CleanedNonEdge.OrReaches n C (n + j) g ↔ j < C.gates.length ∧ (g = j ∨
      ((gateAt C j).op = GateOp.or ∧ ∃ w ∈ (gateAt C j).inputs, w < n + j ∧
        PEqualNP.CleanedNonEdge.OrReaches n C w g)) := by
  have h := orSets_char n C.gates g j
  unfold PEqualNP.CleanedNonEdge.OrReaches PEqualNP.CleanedNonEdge.orSets gateAt
  have e : n + j - n = j := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, h0, h3 | ⟨hop, w, hw, h1, h2, h3⟩⟩
    · exact ⟨h0, Or.inl h3⟩
    · exact ⟨h0, Or.inr ⟨hop, w, hw, h2, h1, h3⟩⟩
  · rintro ⟨h0, h3 | ⟨hop, w, hw, h2, h1, h3⟩⟩
    · exact ⟨by omega, h0, Or.inl h3⟩
    · exact ⟨by omega, h0, Or.inr ⟨hop, w, hw, h1, h2, h3⟩⟩
lemma orReaches_orR (n : ℕ) (C : Circuit) (g : ℕ) :
    ∀ w, PEqualNP.CleanedNonEdge.OrReaches n C w g →
      OrR n C w (n + g) ∧ g < C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    have hw : n ≤ w := h.1
    obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    rw [orReaches_iff] at h
    obtain ⟨hj, h3 | ⟨hop, w2, hw2, hlt, h3⟩⟩ := h
    · subst h3; exact ⟨Relation.ReflTransGen.refl, hj⟩
    · obtain ⟨h4, h5⟩ := ih w2 hlt h3
      exact ⟨Relation.ReflTransGen.head ⟨j, rfl, hj, hop, hw2⟩ h4, h5⟩
lemma orR_orReaches (n : ℕ) (C : Circuit) (hA : AO n C) (g : ℕ) (hg : g < C.gates.length)
    (w : ℕ) (h : OrR n C w (n + g)) : PEqualNP.CleanedNonEdge.OrReaches n C w g := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => rw [orReaches_iff]; exact ⟨hg, Or.inl rfl⟩
  | head h1 h2 ih =>
    have hlt := orStep_lt n C hA _ _ h1
    obtain ⟨k, rfl, hk, hop, hin⟩ := h1
    rw [orReaches_iff]
    exact ⟨hk, Or.inr ⟨hop, _, hin, hlt, ih⟩⟩
lemma mem_orIn (n : ℕ) (C : Circuit) (hA : AO n C) (w : ℕ) (i : Fin n) :
    i ∈ PEqualNP.TopForm.orIn n C w ↔ OrR n C w i.val := by
  unfold PEqualNP.TopForm.orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (h | ⟨k, hk, hr, hop, hin⟩)
    · rw [h]; exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.tail (orReaches_orR n C k w hr).1 ⟨k, rfl, hk, hop, hin⟩
  · intro h
    rcases Relation.ReflTransGen.cases_tail h with h2 | ⟨c, h2, ⟨k, rfl, hk, hop, hin⟩⟩
    · exact Or.inl h2
    · exact Or.inr ⟨k, hk, orR_orReaches n C hA k hk w h2, hop, hin⟩
lemma ao_of (n : ℕ) (C : Circuit) (h : PEqualNP.TopForm.IsAO2 n C) : AO n C := by
  obtain ⟨h1, h2, h3⟩ := h
  intro k hk
  have hmem : gateAt C k ∈ C.gates := by rw [gateAt_eq C k hk]; exact List.getElem_mem hk
  refine ⟨h1 _ hmem, ?_⟩
  have hl := h3 _ hmem
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hl
  exact ⟨a, b, hab, h2 k hk a (by rw [hab]; simp), h2 k hk b (by rw [hab]; simp)⟩
lemma ao_to (n : ℕ) (C : Circuit) (h : AO n C) : PEqualNP.TopForm.IsAO2 n C := by
  have key : ∀ g ∈ C.gates, ∃ k, k < C.gates.length ∧ g = gateAt C k := by
    intro g hg
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
    exact ⟨k, hk, (gateAt_eq C k hk).symm⟩
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨k, hk, rfl⟩ := key g hg
    exact (h k hk).1
  · intro j hj i hi
    obtain ⟨_, a, b, hab, ha, hb⟩ := h j hj
    rw [hab] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> assumption
  · intro g hg
    obtain ⟨k, hk, rfl⟩ := key g hg
    obtain ⟨_, a, b, hab, _, _⟩ := h k hk
    rw [hab]; rfl
lemma least_of (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h : PEqualNP.TopForm.IsLeastAO G C) : Least n C := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨ao_of n C h1, ?_⟩
  intro D hD hfun
  have hD2 : circuitFun n D = graphFun G ∅ := by
    rw [← h2]; funext x; exact hfun x
  exact h3 D (ao_to n D hD) hD2
lemma bel_iff (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h2 : circuitFun n C = graphFun G ∅) (j : ℕ) :
    Bel n C j ↔ PEqualNP.TopForm.BelowF G C j := by
  unfold Bel PEqualNP.TopForm.BelowF
  constructor
  · intro h x hx
    rw [← h2]; exact h x hx
  · intro h x hx
    have h3 := h x hx
    rw [← h2] at h3; exact h3
lemma mem_junk (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (h : ℕ) :
    h ∈ PEqualNP.TopForm.junk G C ↔ h < C.gates.length ∧ (gateAt C h).op = GateOp.and ∧
      h < C.gates.length ∧
      ∃ x : Fin n → Bool, PEqualNP.EdgeOwnership.gateVal n C h x = true ∧ graphFun G ∅ x = false := by
  unfold PEqualNP.TopForm.junk PEqualNP.TopForm.gatesWhere
  rw [Finset.mem_filter, Finset.mem_range]
  rfl
open PEqualNP.EdgeOwnership in
theorem final (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : PEqualNP.TopForm.IsLeastAO G C) (hT : PEqualNP.TopForm.TopForm G C) (g : ℕ)
    (hj : PEqualNP.TopForm.junk G C = {g}) (a : ℕ) (ha : a ∈ PEqualNP.TopForm.centreless G C) :
    ∃ b : Fin 2, PEqualNP.TopForm.opnd C a b = n + g ∧
      (PEqualNP.TopForm.side (n := n) C a (1 - b)).Nonempty ∧
      PEqualNP.TopForm.side (n := n) C a (1 - b) ⊆ PEqualNP.TopForm.wmax G C g ∧
      ∀ v w : Fin n, PEqualNP.EdgeOwnership.gateVal n C a (PEqualNP.EdgeOwnership.pairInput v w) = true →
        PEqualNP.EdgeOwnership.gateVal n C g (PEqualNP.EdgeOwnership.pairInput v w) = true ∧
        (v ∈ PEqualNP.TopForm.side (n := n) C a (1 - b) ∨ w ∈ PEqualNP.TopForm.side (n := n) C a (1 - b)) := by
  have hfun := hL.2.1
  have hLeast := least_of n G C hL
  have hA := hLeast.1
  rw [PEqualNP.TopForm.centreless, Finset.mem_filter] at ha
  obtain ⟨hat, hside⟩ := ha
  simp only [PEqualNP.TopForm.tops, PEqualNP.TopForm.gatesWhere, Finset.mem_filter,
    Finset.mem_range] at hat
  obtain ⟨halen, haop, habel⟩ := hat
  have hgj : g ∈ PEqualNP.TopForm.junk G C := by rw [hj]; exact Finset.mem_singleton_self g
  rw [mem_junk] at hgj
  obtain ⟨hglen, hgop, _, x0, hx0, hx0f⟩ := hgj
  have hgb : ¬ Bel n C g := by
    intro hb
    have h3 := (bel_iff n G C hfun g).mp hb x0 hx0
    rw [hx0f] at h3
    exact absurd h3 (by simp)
  have hJ : ∀ h, h < C.gates.length → (gateAt C h).op = GateOp.and → ¬ Bel n C h → h = g := by
    intro h hh hop hnb
    have hm : h ∈ PEqualNP.TopForm.junk G C := by
      rw [mem_junk]
      refine ⟨hh, hop, hh, ?_⟩
      by_contra hcon
      apply hnb
      rw [bel_iff n G C hfun h]
      intro x hx
      by_contra hf
      exact hcon ⟨x, hx, by simpa using hf⟩
    rw [hj] at hm
    exact Finset.mem_singleton.mp hm
  have hT2 : ∀ h, h < C.gates.length → InCone n C h a → (gateAt C h).op = GateOp.and →
      ¬ Bel n C h := by
    intro h hh hc hop hb
    exact hT h hh a halen hop ((bel_iff n G C hfun h).mp hb) haop hc
  have hBa : Bel n C a := (bel_iff n G C hfun a).mpr habel
  obtain ⟨_, a1, b1, hab, _, _⟩ := hA a halen
  have ho0 : PEqualNP.TopForm.opnd C a 0 = a1 := by simp [PEqualNP.TopForm.opnd, hab]
  have ho1 : PEqualNP.TopForm.opnd C a 1 = b1 := by simp [PEqualNP.TopForm.opnd, hab]
  have key : ∀ p q, ((gateAt C a).inputs = [p, q] ∨ (gateAt C a).inputs = [q, p]) →
      PEqualNP.TopForm.orIn n C p = ∅ →
      p = n + g ∧ (PEqualNP.TopForm.orIn n C q).Nonempty ∧
        PEqualNP.TopForm.orIn n C q ⊆ PEqualNP.TopForm.wmax G C g ∧
        ∀ v w : Fin n, gateVal n C a (pairInput v w) = true →
          gateVal n C g (pairInput v w) = true ∧
          (v ∈ PEqualNP.TopForm.orIn n C q ∨ w ∈ PEqualNP.TopForm.orIn n C q) := by
    intro p q hin hp
    have hp2 : ∀ w, w < n → ¬ OrR n C p w := by
      intro w hw hr
      have h3 : (⟨w, hw⟩ : Fin n) ∈ PEqualNP.TopForm.orIn n C p :=
        (mem_orIn n C hA p ⟨w, hw⟩).mpr hr
      rw [hp] at h3
      simp at h3
    obtain ⟨c1, ⟨w0, hw0, hr0⟩, c3, c4⟩ :=
      core n C hLeast a g p q halen haop hin hBa hT2 hJ hgb hp2
    refine ⟨c1, ⟨⟨w0, hw0⟩, (mem_orIn n C hA q ⟨w0, hw0⟩).mpr hr0⟩, ?_, ?_⟩
    · intro w hw
      rw [mem_orIn n C hA q w] at hw
      simp only [PEqualNP.TopForm.wmax, Finset.mem_filter, Finset.mem_univ, true_and]
      intro x hgx hxw
      exact habel x ((c4 x).mpr ⟨hgx, w, hw, hxw⟩)
    · intro v w hv
      obtain ⟨h1, u, hu1, hu2⟩ := (c4 (pairInput v w)).mp hv
      refine ⟨h1, ?_⟩
      simp only [pairInput, decide_eq_true_eq] at hu2
      rcases hu2 with rfl | rfl
      · exact Or.inl ((mem_orIn n C hA q u).mpr hu1)
      · exact Or.inr ((mem_orIn n C hA q u).mpr hu1)
  rcases hside with hs | hs
  · refine ⟨0, ?_⟩
    have e : (1 : Fin 2) - 0 = 1 := by decide
    rw [e]
    simp only [PEqualNP.TopForm.side] at hs ⊢
    rw [ho0] at hs ⊢
    rw [ho1]
    exact key a1 b1 (Or.inl hab) hs
  · refine ⟨1, ?_⟩
    have e : (1 : Fin 2) - 1 = 0 := by decide
    rw [e]
    simp only [PEqualNP.TopForm.side] at hs ⊢
    rw [ho1] at hs ⊢
    rw [ho0]
    exact key b1 a1 (Or.inr hab) hs
end M1503
theorem thm_1503 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
  G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
  ∀ (g : ℕ), PEqualNP.TopForm.junk G C = {g} → ∀ (a : ℕ), a ∈ PEqualNP.TopForm.centreless G C →
    ∃ b : Fin 2, PEqualNP.TopForm.opnd C a b = n + g ∧
      (PEqualNP.TopForm.side (n := n) C a (1 - b)).Nonempty ∧
      PEqualNP.TopForm.side (n := n) C a (1 - b) ⊆ PEqualNP.TopForm.wmax G C g ∧
      ∀ v w : Fin n, PEqualNP.EdgeOwnership.gateVal n C a (PEqualNP.EdgeOwnership.pairInput v w) = true →
        PEqualNP.EdgeOwnership.gateVal n C g (PEqualNP.EdgeOwnership.pairInput v w) = true ∧
        (v ∈ PEqualNP.TopForm.side (n := n) C a (1 - b) ∨ w ∈ PEqualNP.TopForm.side (n := n) C a (1 - b)) := by
  intro n G _ C _ hL hT g hj a ha
  exact PEqualNP.Outside.L_meta_2448_aux.foundation.M1503.final n G C hL hT g hj a ha

namespace M1505
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open M1528.P1.S98
def Reach (n : ℕ) (C : Circuit) : ℕ → ℕ → Prop :=
  Relation.ReflTransGen (fun k k' : ℕ =>
    (gateAt C k).op = GateOp.or ∧ n + k' ∈ (gateAt C k).inputs)
lemma reach_lt (n : ℕ) (C : Circuit) (hA : AO n C) (k k' : ℕ) (hk : k < C.gates.length)
    (h : Reach n C k k') : k' ≤ k := by
  induction h with
  | refl => exact le_rfl
  | @tail b c _ hbc ih =>
    by_cases hb : b < C.gates.length
    · obtain ⟨_, a, b', hin, ha, hb'⟩ := hA b hb
      have hm := hbc.2
      rw [hin] at hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      omega
    · omega
lemma reach_last (n : ℕ) (C : Circuit) (k g : ℕ) (h : Reach n C k g) (hne : k ≠ g) :
    ∃ m, Reach n C k m ∧ (gateAt C m).op = GateOp.or ∧ n + g ∈ (gateAt C m).inputs := by
  rcases Relation.ReflTransGen.cases_tail h with h1 | ⟨m, hm, hstep⟩
  · exact absurd h1.symm hne
  · exact ⟨m, hm, hstep.1, hstep.2⟩
lemma cone_const (n : ℕ) (C : Circuit) (hA : AO n C) (g : ℕ) (x : Fin n → Bool) :
    ∀ k, k < C.gates.length →
      (∀ k', Reach n C k k' → k' = g ∨
        ((gateAt C k').op = GateOp.or ∧ ∀ w ∈ (gateAt C k').inputs, n ≤ w)) →
      W n C x (n + k) = W n C x (n + g) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk hall
    rcases hall k Relation.ReflTransGen.refl with h | ⟨hop, hin⟩
    · rw [h]
    · obtain ⟨_, a, b, hab, ha, hb⟩ := hA k hk
      have hna : n ≤ a := hin a (by simp [hab])
      have hnb : n ≤ b := hin b (by simp [hab])
      have key : ∀ w, w ∈ (gateAt C k).inputs → n ≤ w → w < n + k →
          W n C x w = W n C x (n + g) := by
        intro w hw hnw hwk
        have hw' : w = n + (w - n) := by omega
        rw [hw']
        apply ih (w - n) (by omega) (by omega)
        intro k' hk'
        apply hall k'
        exact Relation.ReflTransGen.head ⟨hop, by rw [← hw']; exact hw⟩ hk'
      rw [W_or n C x k hk hop a b hab ha hb, key a (by simp [hab]) hna ha,
        key b (by simp [hab]) hnb hb]
      simp
lemma leaf_exists (n : ℕ) (C : Circuit) (hL : Least n C) (g k : ℕ) (hg : g < C.gates.length)
    (hk : k < C.gates.length) (hkg : k ≠ g) :
    ∃ k', Reach n C k k' ∧ k' ≠ g ∧
      ((gateAt C k').op ≠ GateOp.or ∨ ∃ w ∈ (gateAt C k').inputs, w < n) := by
  by_contra hno
  have hall : ∀ k', Reach n C k k' → k' = g ∨
      ((gateAt C k').op = GateOp.or ∧ ∀ w ∈ (gateAt C k').inputs, n ≤ w) := by
    intro k' hk'
    by_cases h : k' = g
    · exact Or.inl h
    · right
      constructor
      · by_contra hop
        exact hno ⟨k', hk', h, Or.inl hop⟩
      · intro w hw
        by_contra hlt
        exact hno ⟨k', hk', h, Or.inr ⟨w, hw, by omega⟩⟩
  rcases Nat.lt_or_gt_of_ne hkg with h | h
  · obtain ⟨x, hx⟩ := least_nodup n C hL (n + k) g (by omega) hg
    exact hx (cone_const n C hL.1 g x k hk hall)
  · obtain ⟨x, hx⟩ := least_nodup n C hL (n + g) k (by omega) hk
    exact hx (cone_const n C hL.1 g x k hk hall).symm
lemma step_lt (n : ℕ) (C : Circuit) (hA : AO n C) (k c : ℕ) (hk : k < C.gates.length)
    (hm : n + c ∈ (gateAt C k).inputs) : c < k := by
  obtain ⟨_, a, b', hin, ha, hb'⟩ := hA k hk
  rw [hin] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  omega
open PEqualNP.EdgeOwnership in
lemma reach_inCone (n : ℕ) (C : Circuit) (hA : AO n C) (k k' : ℕ)
    (h : Reach n C k k') : k < C.gates.length → (k' = k ∨ InCone n C k' k) := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => intro _; exact Or.inl rfl
  | @head a c hstep hrest ih =>
    intro hk
    have hca : c < a := step_lt n C hA a c hk hstep.2
    have h1 : InCone n C c a := inCone_c1 n C hA c a hk hstep.2
    rcases ih (by omega) with h | h
    · right; rw [h]; exact h1
    · right
      exact inCone_c2 n C hA k' c a hk h hstep.2
open PEqualNP.EdgeOwnership in
theorem main_abs (n : ℕ) (C : Circuit) (hL : Least n C) (g k0 a : ℕ)
    (hg : g < C.gates.length) (hgand : (gateAt C g).op = GateOp.and)
    (ha : a < C.gates.length) (hread : n + k0 ∈ (gateAt C a).inputs)
    (hreach : Reach n C k0 g) (hne : k0 ≠ g)
    (hleaf : ∀ k', k' < C.gates.length → InCone n C k' a → (gateAt C k').op = GateOp.and →
      k' = g) :
    ∃ m, Reach n C k0 m ∧ (gateAt C m).op = GateOp.or ∧ n + g ∈ (gateAt C m).inputs ∧
      m < C.gates.length ∧
      ∃ y ∈ (gateAt C m).inputs, y ≠ n + g ∧
        (y < n ∨ ∃ k1 k' w, y = n + k1 ∧ Reach n C k1 k' ∧
          (gateAt C k').op = GateOp.or ∧ w ∈ (gateAt C k').inputs ∧ w < n) := by
  have hA := hL.1
  have hk0a : k0 < a := step_lt n C hA a k0 ha hread
  have hk0 : k0 < C.gates.length := by omega
  obtain ⟨m, hm, hop, hin⟩ := reach_last n C k0 g hreach hne
  have hmk : m ≤ k0 := reach_lt n C hA k0 m hk0 hm
  have hml : m < C.gates.length := by omega
  have hgm : g < m := step_lt n C hA m g hml hin
  refine ⟨m, hm, hop, hin, hml, ?_⟩
  obtain ⟨k', hk', hk'g, hcase⟩ := leaf_exists n C hL g m hg hml (by omega)
  rcases Relation.ReflTransGen.cases_head hk' with h | ⟨k1, hstep, hrest⟩
  · subst h
    rcases hcase with h | ⟨w, hw, hwn⟩
    · exact absurd hop h
    · exact ⟨w, hw, by omega, Or.inl hwn⟩
  · have hk1m : k1 < m := step_lt n C hA m k1 hml hstep.2
    have hk1g : k1 ≠ g := by
      intro h
      subst h
      rcases Relation.ReflTransGen.cases_head hrest with h | ⟨c, hc, _⟩
      · exact hk'g h.symm
      · rw [hgand] at hc
        exact absurd hc.1 (by simp)
    refine ⟨n + k1, hstep.2, by omega, Or.inr ?_⟩
    have hk'k1 : k' ≤ k1 := reach_lt n C hA k1 k' (by omega) hrest
    by_cases hopk : (gateAt C k').op = GateOp.or
    · rcases hcase with h | ⟨w, hw, hwn⟩
      · exact absurd hopk h
      · exact ⟨k1, k', w, rfl, hrest, hopk, hw, hwn⟩
    · exfalso
      have hand : (gateAt C k').op = GateOp.and := by
        rcases (hA k' (by omega)).1 with h | h
        · exact h
        · exact absurd h hopk
      have hall : Reach n C k0 k' := Relation.ReflTransGen.trans hm hk'
      have hcone : InCone n C k' a := by
        rcases reach_inCone n C hA k0 k' hall hk0 with h | h
        · rw [h]; exact inCone_c1 n C hA k0 a ha hread
        · exact inCone_c2 n C hA k' k0 a ha h hread
      exact hk'g (hleaf k' (by omega) hcone hand)
open PEqualNP.CleanedNonEdge in
lemma orFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega
open PEqualNP.CleanedNonEdge in
lemma orStep_mem_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) (x : ℕ) :
    x ∈ (orStep n cs g).getD cs.length [] ↔ x = cs.length ∨ (g.op = GateOp.or ∧
      ∃ w ∈ g.inputs, n ≤ w ∧ w < n + cs.length ∧ x ∈ cs.getD (w - n) []) := by
  by_cases h : g.op = GateOp.or
  · simp only [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl, h,
      ↓reduceIte, true_and, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some,
      List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro (h1 | ⟨w, ⟨hw, hn, hlt⟩, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, hw, hn, hlt, hx⟩
    · rintro (h1 | ⟨w, hw, hn, hlt, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, ⟨hw, hn, hlt⟩, hx⟩
  · simp [orStep, List.getD_eq_getElem?_getD, h]
open PEqualNP.CleanedNonEdge in
lemma orStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (orStep n cs g).getD m [] = cs.getD m [] := by
  simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]
open PEqualNP.CleanedNonEdge in
lemma orFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (orStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (orStep n cs g) (by simp [orStep]; omega)]
    exact orStep_getD_lt n cs g k hk
open PEqualNP.CleanedNonEdge in
lemma orSets_mem_iff (n : ℕ) (C : Circuit) (k x : ℕ) (hk : k < C.gates.length) :
    x ∈ (orSets n C).getD k [] ↔ x = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ x ∈ (orSets n C).getD (w - n) []) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : orSets n C = post.foldl (orStep n) (orStep n (pre.foldl (orStep n) []) gk) := by
    simp only [orSets]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (orStep n) []).length = k := by
    rw [orFold_length]; simp [hpre_len]
  have hl1 : (orStep n (pre.foldl (orStep n) []) gk).length = k + 1 := by
    simp [orStep, hl0]
  have h1 : (orSets n C).getD k [] = (orStep n (pre.foldl (orStep n) []) gk).getD k [] := by
    rw [hc, orFold_getD_lt n post _ k (by omega)]
  have h2 : ∀ m, m < k → (orSets n C).getD m [] = (pre.foldl (orStep n) []).getD m [] := by
    intro m hm
    rw [hc, orFold_getD_lt n post _ m (by omega)]
    exact orStep_getD_lt n _ gk m (by omega)
  have h3 := orStep_mem_last n (pre.foldl (orStep n) []) gk x
  rw [hl0] at h3
  rw [h1, h3]
  constructor
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [h2 (w - n) (by omega)]; exact hx⟩
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [← h2 (w - n) (by omega)]; exact hx⟩
open PEqualNP.CleanedNonEdge in
lemma orSets_reach (n : ℕ) (C : Circuit) :
    ∀ k, k < C.gates.length → ∀ x, x ∈ (orSets n C).getD k [] → Reach n C k x := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk x hx
    rcases (orSets_mem_iff n C k x hk).1 hx with h | ⟨hop, w, hw, hn, hlt, hx'⟩
    · rw [h]; exact Relation.ReflTransGen.refl
    · have hw' : n + (w - n) = w := by omega
      exact Relation.ReflTransGen.head ⟨hop, by rw [hw']; exact hw⟩
        (ih (w - n) (by omega) (by omega) x hx')
open PEqualNP.CleanedNonEdge in
lemma orReaches_reach (n : ℕ) (C : Circuit) (w g : ℕ) (h : OrReaches n C w g) :
    n ≤ w ∧ w - n < C.gates.length ∧ Reach n C (w - n) g := by
  obtain ⟨hn, hmem⟩ := h
  have hlt : w - n < C.gates.length := by
    by_contra hge
    have hlen : (orSets n C).length = C.gates.length := by simp [orSets, orFold_length]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hmem
    simp at hmem
  exact ⟨hn, hlt, orSets_reach n C _ hlt g hmem⟩
open PEqualNP.CleanedNonEdge in
lemma reach_orReaches (n : ℕ) (C : Circuit) (hA : AO n C) (k x : ℕ) (h : Reach n C k x) :
    k < C.gates.length → OrReaches n C (n + k) x := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro hk
    refine ⟨by omega, ?_⟩
    rw [Nat.add_sub_cancel_left]
    exact (orSets_mem_iff n C _ _ hk).2 (Or.inl rfl)
  | @head a c hstep hrest ih =>
    intro hk
    have hca : c < a := step_lt n C hA a c hk hstep.2
    have h1 := (ih (by omega)).2
    rw [Nat.add_sub_cancel_left] at h1
    refine ⟨by omega, ?_⟩
    rw [Nat.add_sub_cancel_left]
    refine (orSets_mem_iff n C a x hk).2
      (Or.inr ⟨hstep.1, n + c, hstep.2, by omega, by omega, ?_⟩)
    rw [Nat.add_sub_cancel_left]
    exact h1
open PEqualNP.TopForm PEqualNP.EdgeOwnership in
lemma ao_of (n : ℕ) (C : Circuit) (h : IsAO2 n C) : AO n C := by
  obtain ⟨hao, hrb, hlen⟩ := h
  intro k hk
  have hmem : gateAt C k ∈ C.gates := by rw [gateAt_eq C k hk]; exact List.getElem_mem hk
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (hlen _ hmem)
  refine ⟨hao _ hmem, a, b, hab, ?_, ?_⟩
  · exact hrb k hk a (by simp [hab])
  · exact hrb k hk b (by simp [hab])
open PEqualNP.TopForm PEqualNP.EdgeOwnership in
lemma ao_to (n : ℕ) (C : Circuit) (h : AO n C) : IsAO2 n C := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
    have h1 := (h k hk).1
    rwa [gateAt_eq C k hk] at h1
  · intro j hj i hi
    obtain ⟨_, a, b, hab, ha, hb⟩ := h j hj
    rw [hab] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h1 | h1
    · rw [h1]; exact ha
    · rw [h1]; exact hb
  · intro g hg
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
    obtain ⟨_, a, b, hab, _, _⟩ := h k hk
    rw [gateAt_eq C k hk] at hab
    simp [hab]
open PEqualNP.TopForm PEqualNP.EdgeOwnership in
lemma least_of {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h : IsLeastAO G C) : Least n C := by
  obtain ⟨hao, hfun, hmin⟩ := h
  refine ⟨ao_of n C hao, ?_⟩
  intro D hD hDC
  have h1 : circuitFun n D = graphFun G ∅ := by
    rw [← hfun]
    funext x
    exact hDC x
  exact hmin D (ao_to n D hD) h1
open PEqualNP.TopForm PEqualNP.CleanedNonEdge in
lemma orIn_and (n : ℕ) (C : Circuit) (g : ℕ)
    (hgand : (gateAt C g).op = GateOp.and) : orIn n C (n + g) = ∅ := by
  by_contra hne
  obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  rcases hi with h | ⟨k, hk, hreach, hop, _⟩
  · have := i.isLt
    omega
  · obtain ⟨_, _, hR⟩ := orReaches_reach n C _ _ hreach
    rw [Nat.add_sub_cancel_left] at hR
    rcases Relation.ReflTransGen.cases_head hR with h | ⟨c, hc, _⟩
    · rw [← h, hgand] at hop
      exact absurd hop (by simp)
    · rw [hgand] at hc
      exact absurd hc.1 (by simp)
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge in
theorem final (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hLA : IsLeastAO G C) (hT : TopForm G C) (g : ℕ) (hjunk : junk G C = {g})
    (a : ℕ) (ha : a ∈ tops G C) (b : Fin 2)
    (hreach : OrReaches n C (opnd C a b) g) (hside : (side (n := n) C a b).Nonempty) :
    ∃ m ∈ mixing G C, OrReaches n C (opnd C a b) m ∧ n + g ∈ (gateAt C m).inputs := by
  have hL : Least n C := least_of G C hLA
  have hA := hL.1
  have hgj : g ∈ junk G C := by rw [hjunk]; exact Finset.mem_singleton_self g
  simp only [junk, gatesWhere, Finset.mem_filter, Finset.mem_range] at hgj
  obtain ⟨hg, hgand, _, xg, hxg1, hxg0⟩ := hgj
  simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha
  obtain ⟨hal, haand, haB⟩ := ha
  obtain ⟨hnw, hk0l', hR'⟩ := orReaches_reach n C _ _ hreach
  obtain ⟨k0, hw⟩ : ∃ k0, opnd C a b = n + k0 := ⟨opnd C a b - n, by omega⟩
  have hk0e : opnd C a b - n = k0 := by omega
  rw [hk0e] at hk0l' hR'
  have hread : n + k0 ∈ (gateAt C a).inputs := by
    rw [← hw]
    obtain ⟨_, p, q, hpq, _, _⟩ := hA a hal
    unfold opnd
    rw [hpq]
    obtain ⟨bv, hb⟩ := b
    interval_cases bv <;> simp
  have hemp : orIn n C (n + g) = ∅ := orIn_and n C g hgand
  have hside' : (orIn n C (opnd C a b)).Nonempty := hside
  have hne : k0 ≠ g := by
    intro h
    rw [hw, h, hemp] at hside'
    exact Finset.not_nonempty_empty hside'
  have hleaf : ∀ k', k' < C.gates.length → InCone n C k' a → (gateAt C k').op = GateOp.and →
      k' = g := by
    intro k' hk' hcone hand
    by_cases hB : BelowF G C k'
    · exact absurd hcone (hT k' hk' a hal hand hB haand)
    · have hx : ∃ x, gateVal n C k' x = true ∧ graphFun G ∅ x = false := by
        by_contra hno
        apply hB
        intro x hx
        by_contra hf
        exact hno ⟨x, hx, by simpa using hf⟩
      have hmem : k' ∈ junk G C := by
        simp only [junk, gatesWhere, Finset.mem_filter, Finset.mem_range]
        exact ⟨hk', hand, hk', hx⟩
      rw [hjunk] at hmem
      exact Finset.mem_singleton.mp hmem
  obtain ⟨m, hm, hop, hin, hml, y, hy, hyg, hycase⟩ :=
    main_abs n C hL g k0 a hg hgand hal hread hR' hne hleaf
  refine ⟨m, ?_, ?_, hin⟩
  · obtain ⟨_, p, q, hpq, hp, hq⟩ := hA m hml
    have hynon : (orIn n C y).Nonempty := by
      rcases hycase with hyn | ⟨k1, k', w, hyk, hrk, hopk, hwk, hwn⟩
      · refine ⟨⟨y, hyn⟩, ?_⟩
        simp [orIn]
      · refine ⟨⟨w, hwn⟩, ?_⟩
        simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and]
        right
        rw [hyk] at hy ⊢
        have hk1 : k1 < m := step_lt n C hA m k1 hml hy
        have hk'l : k' ≤ k1 := reach_lt n C hA k1 k' (by omega) hrk
        exact ⟨k', by omega, reach_orReaches n C hA k1 k' hrk (by omega), hopk, hwk⟩
    have hnotB : ¬ BelowF G C m := by
      intro hB
      have h1 : gateVal n C m xg = true := by
        show W n C xg (n + m) = true
        rw [W_or n C xg m hml hop p q hpq hp hq]
        have hgv : W n C xg (n + g) = true := hxg1
        have hin' := hin
        rw [hpq] at hin'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hin'
        rcases hin' with h | h
        · rw [← h, hgv]; simp
        · rw [← h, hgv]; simp
      have h2 := hB xg h1
      rw [hxg0] at h2
      exact absurd h2 (by simp)
    simp only [mixing, orN, gatesWhere, Finset.mem_filter, Finset.mem_range]
    refine ⟨⟨hml, hop, hnotB⟩, ?_⟩
    have h0 : opnd C m 0 = p := by simp [opnd, hpq]
    have h1 : opnd C m 1 = q := by simp [opnd, hpq]
    rw [h0, h1]
    have hin' := hin
    rw [hpq] at hin' hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hin' hy
    rcases hin' with hgp | hgq
    · have hyq : y = q := by
        rcases hy with h | h
        · exact absurd (h.trans hgp.symm) hyg
        · exact h
      rw [← hgp, hemp, ← hyq]
      intro heq
      exact hynon.ne_empty (Eq.mp heq rfl)
    · have hyp : y = p := by
        rcases hy with h | h
        · exact h
        · exact absurd (h.trans hgq.symm) hyg
      rw [← hgq, hemp, ← hyp]
      intro heq
      exact hynon.ne_empty (Eq.mpr heq rfl)
  · rw [hw]
    exact reach_orReaches n C hA k0 m hm hk0l'
end M1505
theorem thm_1505 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
  PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C →
  PEqualNP.TopForm.TopForm G C → ∀ (g : ℕ), PEqualNP.TopForm.junk G C = {g} →
    (∀ a ∈ PEqualNP.TopForm.tops G C, ∀ b : Fin 2,
      PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C a b) g →
      (PEqualNP.TopForm.side (n := n) C a b).Nonempty →
      ∃ m ∈ PEqualNP.TopForm.mixing G C,
        PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C a b) m ∧
        n + g ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C m).inputs) := by
  intro n G _ C _ _ hL hT g hjunk a ha b hreach hside
  exact PEqualNP.Outside.L_meta_2448_aux.foundation.M1505.final n G C hL hT g hjunk a ha b hreach hside

namespace M1506
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open M1528.P1.S98
def OrStep (n : ℕ) (C : Circuit) (u v : ℕ) : Prop :=
  ∃ k, u = n + k ∧ k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧ v ∈ (gateAt C k).inputs
def OrR (n : ℕ) (C : Circuit) : ℕ → ℕ → Prop := Relation.ReflTransGen (OrStep n C)
def Leaf (n : ℕ) (C : Circuit) (v : ℕ) : Prop :=
  v < n ∨ ∃ h, v = n + h ∧ h < C.gates.length ∧ (gateAt C h).op = GateOp.and
lemma orStep_lt (n : ℕ) (C : Circuit) (hA : AO n C) (u v : ℕ) (h : OrStep n C u v) : v < u := by
  obtain ⟨k, rfl, hk, _, hv⟩ := h
  obtain ⟨_, a, b, hin, ha, hb⟩ := hA k hk
  rw [hin] at hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  omega
lemma orR_le (n : ℕ) (C : Circuit) (hA : AO n C) (u v : ℕ) (h : OrR n C u v) : v ≤ u := by
  induction h with
  | refl => exact le_rfl
  | tail _ h2 ih => have := orStep_lt n C hA _ _ h2; omega
lemma orStep_mono (n : ℕ) (C : Circuit) (hA : AO n C) (x : Fin n → Bool) (u v : ℕ)
    (h : OrStep n C u v) (hv : W n C x v = true) : W n C x u = true := by
  obtain ⟨k, rfl, hk, hop, hin⟩ := h
  obtain ⟨_, a, b, hab, ha, hb⟩ := hA k hk
  rw [W_or n C x k hk hop a b hab ha hb]
  rw [hab] at hin
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
  rcases hin with rfl | rfl
  · simp [hv]
  · simp [hv]
lemma orR_mono (n : ℕ) (C : Circuit) (hA : AO n C) (x : Fin n → Bool) (u v : ℕ)
    (h : OrR n C u v) (hv : W n C x v = true) : W n C x u = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head h1 _ ih => exact orStep_mono n C hA x _ _ h1 ih
lemma orR_leaf_true (n : ℕ) (C : Circuit) (hA : AO n C) (x : Fin n → Bool) :
    ∀ u, u < n + C.gates.length → W n C x u = true →
      ∃ v, OrR n C u v ∧ Leaf n C v ∧ W n C x v = true := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu hx
    by_cases h1 : u < n
    · exact ⟨u, Relation.ReflTransGen.refl, Or.inl h1, hx⟩
    · obtain ⟨k, rfl⟩ : ∃ k, u = n + k := ⟨u - n, by omega⟩
      have hk : k < C.gates.length := by omega
      obtain ⟨hop, a, b, hab, ha, hb⟩ := hA k hk
      rcases hop with hop | hop
      · exact ⟨n + k, Relation.ReflTransGen.refl, Or.inr ⟨k, rfl, hk, hop⟩, hx⟩
      · rw [W_or n C x k hk hop a b hab ha hb] at hx
        simp only [Bool.or_eq_true] at hx
        rcases hx with hx | hx
        · obtain ⟨v, hv1, hv2, hv3⟩ := ih a ha (by omega) hx
          exact ⟨v, Relation.ReflTransGen.head ⟨k, rfl, hk, hop, by rw [hab]; simp⟩ hv1, hv2, hv3⟩
        · obtain ⟨v, hv1, hv2, hv3⟩ := ih b hb (by omega) hx
          exact ⟨v, Relation.ReflTransGen.head ⟨k, rfl, hk, hop, by rw [hab]; simp⟩ hv1, hv2, hv3⟩
open PEqualNP.EdgeOwnership in
lemma orR_cone (n : ℕ) (C : Circuit) (hA : AO n C) (h u : ℕ) (hr : OrR n C u (n + h)) :
    ∀ k, u = n + k → k < C.gates.length → h = k ∨ InCone n C h k := by
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl => intro k hk _; left; omega
  | head h1 h2 ih =>
    rename_i u c
    intro k hk hlen
    have hle := orR_le n C hA _ _ h2
    have hlt := orStep_lt n C hA _ _ h1
    obtain ⟨k', hk', _, _, hin⟩ := h1
    have hkk : k' = k := by omega
    subst hkk
    have hc : c = n + (c - n) := by omega
    rcases ih (c - n) hc (by omega) with h3 | h3
    · right
      refine inCone_c1 n C hA h k' hlen ?_
      rw [h3, ← hc]
      exact hin
    · right
      refine inCone_c2 n C hA h (c - n) k' hlen h3 ?_
      rw [← hc]
      exact hin
lemma W_mono (n : ℕ) (C : Circuit) (hA : AO n C) (x x' : Fin n → Bool)
    (hx : ∀ i, x i = true → x' i = true) :
    ∀ u, u < n + C.gates.length → W n C x u = true → W n C x' u = true := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu h
    by_cases h1 : u < n
    · rw [W_input n C x' u h1]
      rw [W_input n C x u h1] at h
      exact hx _ h
    · obtain ⟨k, rfl⟩ : ∃ k, u = n + k := ⟨u - n, by omega⟩
      have hk : k < C.gates.length := by omega
      obtain ⟨hop, a, b, hab, ha, hb⟩ := hA k hk
      rcases hop with hop | hop
      · rw [W_and n C x k hk hop a b hab ha hb] at h
        rw [W_and n C x' k hk hop a b hab ha hb]
        simp only [Bool.and_eq_true] at h ⊢
        exact ⟨ih a ha (by omega) h.1, ih b hb (by omega) h.2⟩
      · rw [W_or n C x k hk hop a b hab ha hb] at h
        rw [W_or n C x' k hk hop a b hab ha hb]
        simp only [Bool.or_eq_true] at h ⊢
        rcases h with h | h
        · exact Or.inl (ih a ha (by omega) h)
        · exact Or.inr (ih b hb (by omega) h)
open PEqualNP.EdgeOwnership in
lemma leafg (n : ℕ) (C : Circuit) (hA : AO n C) (g : ℕ)
    (hT : ∀ h j, j < C.gates.length → (gateAt C j).op = GateOp.and → InCone n C h j →
      (gateAt C h).op = GateOp.and → ¬ Bel n C h)
    (hJ : ∀ h, h < C.gates.length → (gateAt C h).op = GateOp.and → ¬ Bel n C h → h = g)
    (j p : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and)
    (hp : p ∈ (gateAt C j).inputs) (v : ℕ) (hr : OrR n C p v) (hl : Leaf n C v) :
    v < n ∨ v = n + g := by
  rcases hl with hl | ⟨h, rfl, hh, hhop⟩
  · exact Or.inl hl
  · right
    have hle := orR_le n C hA _ _ hr
    have hplt : p < n + j := by
      obtain ⟨_, a, b, hin, ha, hb⟩ := hA j hj
      rw [hin] at hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      omega
    have hp' : p = n + (p - n) := by omega
    have hc : InCone n C h j := by
      rcases orR_cone n C hA h p hr (p - n) hp' (by omega) with h3 | h3
      · refine inCone_c1 n C hA h j hj ?_
        rw [h3, ← hp']
        exact hp
      · refine inCone_c2 n C hA h (p - n) j hj h3 ?_
        rw [← hp']
        exact hp
    rw [hJ h hh hhop (hT h j hj hop hc hhop)]
lemma up (n : ℕ) (C : Circuit) (hL : Least n C) (hout : C.output + 1 = n + C.gates.length)
    (g : ℕ) (hg : ¬ Bel n C g) :
    ∀ d k, k + d = C.gates.length → k < C.gates.length →
      (∀ x, W n C x (n + g) = true → W n C x (n + k) = true) →
      ∃ h p, h < C.gates.length ∧ (gateAt C h).op = GateOp.and ∧ p ∈ (gateAt C h).inputs ∧
        OrR n C p (n + k) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro k hd hk hgk
    by_cases hlast : k + 1 = C.gates.length
    · exfalso
      apply hg
      intro x hx
      have h1 := hgk x hx
      have ho : C.output = n + k := by omega
      have h2 : W n C x C.output = true := by rw [ho]; exact h1
      exact h2
    · obtain ⟨r, hkr, hr, hin⟩ := least_read n C hL hout k (by omega)
      obtain ⟨hop, _⟩ := hL.1 r hr
      rcases hop with hop | hop
      · exact ⟨r, n + k, hr, hop, hin, Relation.ReflTransGen.refl⟩
      · obtain ⟨h, p, hh, hhop, hp, hpr⟩ := ih (C.gates.length - r) (by omega) r (by omega) hr
          (fun x hx => orStep_mono n C hL.1 x _ _ ⟨r, rfl, hr, hop, hin⟩ (hgk x hx))
        exact ⟨h, p, hh, hhop, hp, Relation.ReflTransGen.tail hpr ⟨r, rfl, hr, hop, hin⟩⟩
lemma pair_le (n : ℕ) (u : Fin n) (x : Fin n → Bool) (hx : x u = true) :
    ∀ i, PEqualNP.EdgeOwnership.pairInput u u i = true → x i = true := by
  intro i hi
  simp only [PEqualNP.EdgeOwnership.pairInput, or_self, decide_eq_true_eq] at hi
  rw [hi]
  exact hx
open PEqualNP.EdgeOwnership in
theorem part1 (n : ℕ) (C : Circuit) (hL : Least n C)
    (hout : C.output + 1 = n + C.gates.length) (g m y : ℕ)
    (hT : ∀ h j, j < C.gates.length → (gateAt C j).op = GateOp.and → InCone n C h j →
      (gateAt C h).op = GateOp.and → ¬ Bel n C h)
    (hJ : ∀ h, h < C.gates.length → (gateAt C h).op = GateOp.and → ¬ Bel n C h → h = g)
    (hg : ¬ Bel n C g) (hm : m < C.gates.length) (hmop : (gateAt C m).op = GateOp.or)
    (hgm : n + g ∈ (gateAt C m).inputs) (hy : y ∈ (gateAt C m).inputs) (hyg : y ≠ n + g) :
    ∃ u : Fin n, OrR n C y u.val ∧ W n C (pairInput u u) (n + g) = false := by
  have hA := hL.1
  by_contra hno
  push Not at hno
  obtain ⟨_, a, b, hab, ha, hb⟩ := hA m hm
  have hylt : y < n + m := by
    rw [hab] at hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    omega
  have hglt : n + g < n + m := by
    rw [hab] at hgm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hgm
    omega
  have hWm : ∀ x, W n C x (n + m) = (W n C x (n + g) || W n C x y) := by
    intro x
    rw [W_or n C x m hm hmop a b hab ha hb]
    rw [hab] at hy hgm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy hgm
    rcases hgm with h1 | h1 <;> rcases hy with h2 | h2
    · exact absurd (h2.trans h1.symm) hyg
    · rw [← h1, ← h2]
    · rw [← h1, ← h2, Bool.or_comm]
    · exact absurd (h2.trans h1.symm) hyg
  have hgm' : ∀ x, W n C x (n + g) = true → W n C x (n + m) = true := by
    intro x hx
    rw [hWm x, hx]
    rfl
  obtain ⟨h, p, hh, hhop, hp, hpm⟩ := up n C hL hout g hg (C.gates.length - m) m (by omega) hm hgm'
  have hmy : OrR n C (n + m) y := Relation.ReflTransGen.single ⟨m, rfl, hm, hmop, hy⟩
  have hyle : ∀ x, W n C x y = true → W n C x (n + g) = true := by
    intro x hx
    obtain ⟨v, hv1, hv2, hv3⟩ := orR_leaf_true n C hA x y (by omega) hx
    rcases leafg n C hA g hT hJ h p hh hhop hp v ((hpm.trans hmy).trans hv1) hv2 with h1 | h1
    · have h2 := hno ⟨v, h1⟩ hv1
      simp only [ne_eq, Bool.not_eq_false] at h2
      have h3 : x ⟨v, h1⟩ = true := by
        rw [← W_input n C x v h1]
        exact hv3
      exact W_mono n C hA _ x (pair_le n ⟨v, h1⟩ x h3) (n + g) (by omega) h2
    · rw [← h1]
      exact hv3
  obtain ⟨x, hx⟩ := least_nodup n C hL (n + g) m hglt hm
  apply hx
  rw [hWm x]
  cases hgx : W n C x (n + g) with
  | true => rfl
  | false =>
    cases hyx : W n C x y with
    | true => rw [hyle x hyx] at hgx; exact absurd hgx (by simp)
    | false => rfl
open PEqualNP.EdgeOwnership in
theorem part2 (n : ℕ) (C : Circuit) (hL : Least n C) (g m y a p q : ℕ)
    (hT : ∀ h j, j < C.gates.length → (gateAt C j).op = GateOp.and → InCone n C h j →
      (gateAt C h).op = GateOp.and → ¬ Bel n C h)
    (hJ : ∀ h, h < C.gates.length → (gateAt C h).op = GateOp.and → ¬ Bel n C h → h = g)
    (hg : ¬ Bel n C g) (hm : m < C.gates.length) (hmop : (gateAt C m).op = GateOp.or)
    (hgm : n + g ∈ (gateAt C m).inputs) (hy : y ∈ (gateAt C m).inputs)
    (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and)
    (hin : (gateAt C a).inputs = [p, q] ∨ (gateAt C a).inputs = [q, p])
    (hbel : Bel n C a) (hpm : OrR n C p (n + m))
    (hV : ∀ z : Fin n, C.eval (List.ofFn (pairInput z z)) = false)
    (u : Fin n) (hu : OrR n C y u.val) :
    OrR n C p u.val ∧
    (∀ z : Fin n, OrR n C q z.val →
      C.eval (List.ofFn (pairInput u z)) = true ∧
      ∀ x : Fin n → Bool, W n C x (n + g) = true → x z = true → C.eval (List.ofFn x) = true) ∧
    (∀ v w : Fin n, W n C (pairInput v w) (n + a) = true →
      (∀ v' w' : Fin n, OrR n C p v'.val → OrR n C q w'.val →
        ¬ ((v = v' ∧ w = w') ∨ (v = w' ∧ w = v'))) →
      W n C (pairInput v w) (n + g) = true ∧ ∃ z : Fin n, OrR n C q z.val ∧ (z = v ∨ z = w)) := by
  have hA := hL.1
  obtain ⟨_, a1, b1, hab, ha1, hb1⟩ := hA a ha
  have hpq : p < n + a ∧ q < n + a := by
    rcases hin with h | h
    · rw [h] at hab
      simp only [List.cons.injEq, and_true] at hab
      omega
    · rw [h] at hab
      simp only [List.cons.injEq, and_true] at hab
      omega
  have hmem : ∀ c, c = p ∨ c = q → c ∈ (gateAt C a).inputs := by
    intro c hc
    rcases hin with h | h <;> rw [h] <;> simp <;> tauto
  have hWa : ∀ x, W n C x (n + a) = (W n C x p && W n C x q) := by
    intro x
    rcases hin with h | h
    · exact W_and n C x a ha hop p q h hpq.1 hpq.2
    · rw [W_and n C x a ha hop q p h hpq.2 hpq.1, Bool.and_comm]
  have hmy : OrR n C (n + m) y := Relation.ReflTransGen.single ⟨m, rfl, hm, hmop, hy⟩
  have hmg : OrR n C (n + m) (n + g) := Relation.ReflTransGen.single ⟨m, rfl, hm, hmop, hgm⟩
  have hpu : OrR n C p u.val := (hpm.trans hmy).trans hu
  have hpg : OrR n C p (n + g) := hpm.trans hmg
  have hqg : ¬ OrR n C q (n + g) := by
    intro hq
    apply hg
    intro x hx
    apply hbel x
    rw [hWa x, orR_mono n C hA x _ _ hpg hx, orR_mono n C hA x _ _ hq hx]
    rfl
  have hvar : ∀ (x : Fin n → Bool) (c : ℕ), c = p ∨ c = q → W n C x c = true →
      W n C x (n + g) = false ∨ c = q →
      ∃ z : Fin n, OrR n C c z.val ∧ x z = true := by
    intro x c hc hx hgc
    have hclt : c < n + a := by rcases hc with rfl | rfl <;> omega
    obtain ⟨v, hv1, hv2, hv3⟩ := orR_leaf_true n C hA x c (by omega) hx
    rcases leafg n C hA g hT hJ a c ha hop (hmem c hc) v hv1 hv2 with h1 | h1
    · refine ⟨⟨v, h1⟩, hv1, ?_⟩
      rw [← W_input n C x v h1]
      exact hv3
    · exfalso
      rcases hgc with h2 | h2
      · rw [h1, h2] at hv3
        exact absurd hv3 (by simp)
      · rw [h1, h2] at hv1
        exact hqg hv1
  have hpair : ∀ v w z : Fin n, pairInput v w z = true → z = v ∨ z = w := by
    intro v w z hz
    simpa [pairInput] using hz
  have hpair' : ∀ v w : Fin n, pairInput v w v = true ∧ pairInput v w w = true := by
    intro v w
    simp [pairInput]
  have hWin : ∀ (x : Fin n → Bool) (c : ℕ) (z : Fin n), c < n + C.gates.length →
      OrR n C c z.val → x z = true → W n C x c = true := by
    intro x c z _ hcz hz
    refine orR_mono n C hA x _ _ hcz ?_
    rw [W_input n C x z.val z.isLt]
    exact hz
  refine ⟨hpu, ?_, ?_⟩
  · intro z hz
    refine ⟨?_, ?_⟩
    · apply hbel
      rw [hWa, hWin _ p u (by omega) hpu (hpair' u z).1, hWin _ q z (by omega) hz (hpair' u z).2]
      rfl
    · intro x hx hxz
      apply hbel
      rw [hWa, orR_mono n C hA x _ _ hpg hx, hWin x q z (by omega) hz hxz]
      rfl
  · intro v w hvw hno
    rw [hWa] at hvw
    simp only [Bool.and_eq_true] at hvw
    obtain ⟨z, hz1, hz2⟩ := hvar _ q (Or.inr rfl) hvw.2 (Or.inr rfl)
    have hzvw := hpair v w z hz2
    refine ⟨?_, z, hz1, hzvw⟩
    by_contra hgf
    simp only [Bool.not_eq_true] at hgf
    obtain ⟨z', hz'1, hz'2⟩ := hvar _ p (Or.inl rfl) hvw.1 (Or.inl hgf)
    have hz'vw := hpair v w z' hz'2
    have hne : z' ≠ z := by
      rintro rfl
      have h1 : C.eval (List.ofFn (pairInput z' z')) = true := by
        apply hbel
        rw [hWa, hWin _ p z' (by omega) hz'1 (hpair' z' z').1,
          hWin _ q z' (by omega) hz1 (hpair' z' z').1]
        rfl
      rw [hV z'] at h1
      exact absurd h1 (by simp)
    apply hno z' z hz'1 hz1
    rcases hz'vw with h1 | h1 <;> rcases hzvw with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · exact Or.inl ⟨h1.symm, h2.symm⟩
    · exact Or.inr ⟨h2.symm, h1.symm⟩
    · exact absurd (h1.trans h2.symm) hne
open PEqualNP.EdgeOwnership in
lemma pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
  simp [pairInput]
open PEqualNP.EdgeOwnership in
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
open PEqualNP.EdgeOwnership in
lemma graphFun_diag {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u : Fin n) :
    graphFun G ∅ (pairInput u u) = false := by
  cases h : graphFun G ∅ (pairInput u u) with
  | false => rfl
  | true => exact absurd ((graphFun_pair G u u).mp h) G.irrefl
open PEqualNP.EdgeOwnership in
lemma out_last (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : Least n C) (hF : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = graphFun G ∅ x)
    (hE : G.edgeFinset.Nonempty) : C.output + 1 = n + C.gates.length := by
  refine (least_out n C hL ?_ ?_).2
  · obtain ⟨e, he⟩ := hE
    rw [SimpleGraph.mem_edgeFinset] at he
    induction e using Sym2.ind with
    | _ u v =>
      rw [SimpleGraph.mem_edgeSet] at he
      exact ⟨pairInput u v, by rw [hF]; exact (graphFun_pair G u v).mpr he⟩
  · intro u
    refine ⟨pairInput u u, (pairInput_true u u u).mpr (Or.inl rfl), ?_⟩
    rw [hF]
    exact graphFun_diag G u
open PEqualNP.EdgeOwnership in
theorem main_abs (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : Least n C) (hF : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = graphFun G ∅ x)
    (hE : G.edgeFinset.Nonempty) (g m y : ℕ)
    (hT : ∀ h j, j < C.gates.length → (gateAt C j).op = GateOp.and → InCone n C h j →
      (gateAt C h).op = GateOp.and → ¬ Bel n C h)
    (hJ : ∀ h, h < C.gates.length → (gateAt C h).op = GateOp.and → ¬ Bel n C h → h = g)
    (hg : ¬ Bel n C g) (hm : m < C.gates.length) (hmop : (gateAt C m).op = GateOp.or)
    (hgm : n + g ∈ (gateAt C m).inputs) (hy : y ∈ (gateAt C m).inputs) (hyg : y ≠ n + g) :
    (∃ u : Fin n, OrR n C y u.val ∧ gateVal n C g (pairInput u u) = false) ∧
    ∀ u : Fin n, OrR n C y u.val → ∀ a p q : ℕ, a < C.gates.length →
      (gateAt C a).op = GateOp.and →
      ((gateAt C a).inputs = [p, q] ∨ (gateAt C a).inputs = [q, p]) →
      (∀ x : Fin n → Bool, gateVal n C a x = true → graphFun G ∅ x = true) →
      OrR n C p (n + m) →
      OrR n C p u.val ∧
      (∀ z : Fin n, OrR n C q z.val → G.Adj u z ∧
        ∀ x : Fin n → Bool, gateVal n C g x = true → x z = true → graphFun G ∅ x = true) ∧
      (∀ v w : Fin n, gateVal n C a (pairInput v w) = true →
        (∀ v' w' : Fin n, OrR n C p v'.val → OrR n C q w'.val →
          ¬ ((v = v' ∧ w = w') ∨ (v = w' ∧ w = v'))) →
        gateVal n C g (pairInput v w) = true ∧
          ∃ z : Fin n, OrR n C q z.val ∧ (z = v ∨ z = w)) := by
  have hout := out_last n G C hL hF hE
  refine ⟨part1 n C hL hout g m y hT hJ hg hm hmop hgm hy hyg, ?_⟩
  intro u hu a p q ha hop hin hbelG hpm
  have hbel : Bel n C a := by
    intro x hx
    rw [hF]
    exact hbelG x hx
  have hV : ∀ z : Fin n, C.eval (List.ofFn (pairInput z z)) = false := by
    intro z
    rw [hF]
    exact graphFun_diag G z
  obtain ⟨h1, h2, h3⟩ := part2 n C hL g m y a p q hT hJ hg hm hmop hgm hy ha hop hin hbel hpm hV u hu
  refine ⟨h1, ?_, h3⟩
  intro z hz
  obtain ⟨h4, h5⟩ := h2 z hz
  refine ⟨?_, ?_⟩
  · rw [hF] at h4
    exact (graphFun_pair G u z).mp h4
  · intro x hx hxz
    rw [← hF]
    exact h5 x hx hxz
lemma not_cross {n : ℕ} (S0 S1 : Finset (Fin n)) (v w : Fin n)
    (h : s(v, w) ∉ (S0 ×ˢ S1).image (fun p => s(p.1, p.2))) :
    ∀ v' w' : Fin n, ((v' ∈ S0 ∧ w' ∈ S1) ∨ (v' ∈ S1 ∧ w' ∈ S0)) →
      ¬ ((v = v' ∧ w = w') ∨ (v = w' ∧ w = v')) := by
  intro v' w' hm he
  apply h
  rw [Finset.mem_image]
  rcases hm with ⟨h0, h1⟩ | ⟨h1, h0⟩
  · refine ⟨(v', w'), Finset.mem_product.mpr ⟨h0, h1⟩, ?_⟩
    rcases he with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1, e2]
    · rw [e1, e2]
      exact Sym2.eq_swap
  · refine ⟨(w', v'), Finset.mem_product.mpr ⟨h0, h1⟩, ?_⟩
    rcases he with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1, e2]
      exact Sym2.eq_swap
    · rw [e1, e2]
open PEqualNP.EdgeOwnership in
lemma inCone_lt (n : ℕ) (C : Circuit) :
    ∀ k, k < C.gates.length → ∀ i, InCone n C i k → i < k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk i hc
    rw [inCone_iff n C i k hk] at hc
    obtain ⟨w, _, hn, hlt, h | h⟩ := hc
    · omega
    · have := ih (w - n) (by omega) (by omega) i h
      omega
open PEqualNP.CleanedNonEdge in
lemma cnFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega
open PEqualNP.CleanedNonEdge in
lemma cnStep_mem_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) (x : ℕ) :
    x ∈ (orStep n cs g).getD cs.length [] ↔ x = cs.length ∨ (g.op = GateOp.or ∧
      ∃ w ∈ g.inputs, n ≤ w ∧ w < n + cs.length ∧ x ∈ cs.getD (w - n) []) := by
  by_cases hop : g.op = GateOp.or
  · simp only [orStep, hop, ↓reduceIte, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (le_refl cs.length), Nat.sub_self, List.getElem?_cons_zero,
      Option.getD_some, List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq,
      true_and]
    constructor
    · rintro (h | ⟨w, ⟨hw, hn, hlt⟩, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨w, hw, hn, hlt, h⟩
    · rintro (h | ⟨w, hw, hn, hlt, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨w, ⟨hw, hn, hlt⟩, h⟩
  · simp only [orStep, hop, ↓reduceIte, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (le_refl cs.length), Nat.sub_self, List.getElem?_cons_zero,
      Option.getD_some, List.mem_cons, List.not_mem_nil, or_false, false_and]
open PEqualNP.CleanedNonEdge in
lemma cnStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (orStep n cs g).getD m [] = cs.getD m [] := by
  simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]
open PEqualNP.CleanedNonEdge in
lemma cnFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (orStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (orStep n cs g) (by simp [orStep]; omega)]
    exact cnStep_getD_lt n cs g k hk
open PEqualNP.CleanedNonEdge in
lemma orSets_iff (n : ℕ) (C : Circuit) (g k : ℕ) (hk : k < C.gates.length) :
    g ∈ (orSets n C).getD k [] ↔ g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ g ∈ (orSets n C).getD (w - n) []) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : orSets n C = post.foldl (orStep n) (orStep n (pre.foldl (orStep n) []) gk) := by
    simp only [orSets]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (orStep n) []).length = k := by
    rw [cnFold_length]; simp [hpre_len]
  have hl1 : (orStep n (pre.foldl (orStep n) []) gk).length = k + 1 := by
    simp [orStep, hl0]
  have h1 : (orSets n C).getD k [] = (orStep n (pre.foldl (orStep n) []) gk).getD k [] := by
    rw [hc, cnFold_getD_lt n post _ k (by omega)]
  have h2 : ∀ m, m < k → (orSets n C).getD m [] = (pre.foldl (orStep n) []).getD m [] := by
    intro m hm
    rw [hc, cnFold_getD_lt n post _ m (by omega)]
    exact cnStep_getD_lt n _ gk m (by omega)
  have h3 := cnStep_mem_last n (pre.foldl (orStep n) []) gk g
  rw [hl0] at h3
  rw [h1, h3]
  constructor
  · rintro (h | ⟨hop, w, hw, hn, hlt, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [h2 (w - n) (by omega)]; exact h⟩
  · rintro (h | ⟨hop, w, hw, hn, hlt, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [← h2 (w - n) (by omega)]; exact h⟩
open PEqualNP.CleanedNonEdge in
lemma orSets_len (n : ℕ) (C : Circuit) : (orSets n C).length = C.gates.length := by
  simp only [orSets]
  rw [cnFold_length]
  simp
open PEqualNP.CleanedNonEdge in
lemma reaches_to (n : ℕ) (C : Circuit) :
    ∀ k g, g ∈ (orSets n C).getD k [] → g < C.gates.length ∧ OrR n C (n + k) (n + g) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro g hg
    have hk : k < C.gates.length := by
      by_contra hk
      have hnone : (orSets n C)[k]? = none :=
        List.getElem?_eq_none (by rw [orSets_len]; omega)
      rw [List.getD_eq_getElem?_getD, hnone] at hg
      simp at hg
    rw [orSets_iff n C g k hk] at hg
    rcases hg with rfl | ⟨hop, w, hw, hn, hlt, h⟩
    · exact ⟨hk, Relation.ReflTransGen.refl⟩
    · obtain ⟨h4, h5⟩ := ih (w - n) (by omega) g h
      have hw' : n + (w - n) = w := by omega
      rw [hw'] at h5
      exact ⟨h4, Relation.ReflTransGen.head ⟨k, rfl, hk, hop, hw⟩ h5⟩
open PEqualNP.CleanedNonEdge in
lemma orReaches_iff (n : ℕ) (C : Circuit) (hA : AO n C) (w g : ℕ) :
    OrReaches n C w g ↔ (n ≤ w ∧ g < C.gates.length ∧ OrR n C w (n + g)) := by
  constructor
  · rintro ⟨hn, h⟩
    obtain ⟨h1, h2⟩ := reaches_to n C (w - n) g h
    have hw' : n + (w - n) = w := by omega
    rw [hw'] at h2
    exact ⟨hn, h1, h2⟩
  · rintro ⟨hn, hg, h⟩
    refine ⟨hn, ?_⟩
    clear hn
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl =>
      have he : n + g - n = g := by omega
      rw [he, orSets_iff n C g g hg]
      exact Or.inl rfl
    | head h1 h2 ih =>
      rename_i u c
      have hle := orR_le n C hA _ _ h2
      have hlt := orStep_lt n C hA _ _ h1
      obtain ⟨k, rfl, hk, hop, hin⟩ := h1
      have he : n + k - n = k := by omega
      rw [he, orSets_iff n C g k hk]
      exact Or.inr ⟨hop, c, hin, by omega, hlt, ih⟩
lemma orIn_iff (n : ℕ) (C : Circuit) (hA : AO n C) (w : ℕ) (u : Fin n) :
    u ∈ PEqualNP.TopForm.orIn n C w ↔ OrR n C w u.val := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (h | ⟨k, hk, hr, hop, hin⟩)
    · rw [h]
      exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.tail ((orReaches_iff n C hA w k).mp hr).2.2 ⟨k, rfl, hk, hop, hin⟩
  · intro h
    rcases Relation.ReflTransGen.cases_tail h with h1 | ⟨c, h1, ⟨k, rfl, hk, hop, hin⟩⟩
    · exact Or.inl h1
    · have hle := orR_le n C hA _ _ h1
      exact Or.inr ⟨k, hk, (orReaches_iff n C hA w k).mpr ⟨by omega, hk, h1⟩, hop, hin⟩
lemma ao_of (n : ℕ) (C : Circuit) (h : PEqualNP.TopForm.IsAO2 n C) : AO n C := by
  obtain ⟨h1, h2, h3⟩ := h
  intro k hk
  have hmem : gateAt C k ∈ C.gates := by
    rw [gateAt_eq C k hk]
    exact List.getElem_mem hk
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (h3 _ hmem)
  refine ⟨h1 _ hmem, a, b, hab, ?_, ?_⟩
  · exact h2 k hk a (by rw [hab]; simp)
  · exact h2 k hk b (by rw [hab]; simp)
lemma ao_to (n : ℕ) (D : Circuit) (h : AO n D) : PEqualNP.TopForm.IsAO2 n D := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
    rw [← gateAt_eq D k hk]
    exact (h k hk).1
  · intro j hj i hi
    obtain ⟨_, a, b, hab, ha, hb⟩ := h j hj
    rw [hab] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> assumption
  · intro g hg
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
    obtain ⟨_, a, b, hab, _⟩ := h k hk
    rw [← gateAt_eq D k hk, hab]
    rfl
lemma fin2_cases (t : Fin 2) : (t = 0 ∧ 1 - t = 1) ∨ (t = 1 ∧ 1 - t = 0) := by
  revert t
  decide
lemma mem_wmax {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (g : ℕ)
    (z : Fin n)
    (h : ∀ x : Fin n → Bool, PEqualNP.EdgeOwnership.gateVal n C g x = true → x z = true →
      graphFun G ∅ x = true) : z ∈ PEqualNP.TopForm.wmax G C g := by
  simp only [PEqualNP.TopForm.wmax, Finset.mem_filter, Finset.mem_univ, true_and]
  exact h
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge in
theorem final (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hE : G.edgeFinset.Nonempty) (hLeast : PEqualNP.TopForm.IsLeastAO G C)
    (hTop : PEqualNP.TopForm.TopForm G C) (g : ℕ) (hjunk : PEqualNP.TopForm.junk G C = {g})
    (m : ℕ) (hmix : m ∈ PEqualNP.TopForm.mixing G C)
    (hgm : n + g ∈ (gateAt C m).inputs) (y : ℕ) (hy : y ∈ (gateAt C m).inputs)
    (hyg : y ≠ n + g) :
    (∃ u ∈ PEqualNP.TopForm.orIn n C y, gateVal n C g (pairInput u u) = false) ∧
      ∀ u ∈ PEqualNP.TopForm.orIn n C y, ∀ a ∈ PEqualNP.TopForm.tops G C, ∀ t : Fin 2,
        OrReaches n C (PEqualNP.TopForm.opnd C a t) m →
          u ∈ PEqualNP.TopForm.side (n := n) C a t ∧
          (∀ v w : Fin n, G.Adj v w →
            gateVal n C a (pairInput v w) = true →
            s(v, w) ∉ (PEqualNP.TopForm.side (n := n) C a 0 ×ˢ
              PEqualNP.TopForm.side (n := n) C a 1).image (fun p => s(p.1, p.2)) →
            gateVal n C g (pairInput v w) = true ∧
            ∃ z ∈ PEqualNP.TopForm.wmax G C g, G.Adj u z ∧ (z = v ∨ z = w)) ∧
          (PEqualNP.TopForm.side (n := n) C a t = {u} →
            PEqualNP.TopForm.side (n := n) C a (1 - t) ⊆ PEqualNP.TopForm.wmax G C g) := by
  have hA : AO n C := ao_of n C hLeast.1
  have hF : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = graphFun G ∅ x :=
    fun x => congrFun hLeast.2.1 x
  have hL : Least n C := ⟨hA, fun D hD hfun =>
    hLeast.2.2 D (ao_to n D hD) (funext fun x => (hfun x).trans (hF x))⟩
  have hgj : g ∈ PEqualNP.TopForm.junk G C := by
    rw [hjunk]
    exact Finset.mem_singleton_self g
  have hgj2 : (gateAt C g).op = GateOp.and ∧ (g < C.gates.length ∧
      ∃ x : Fin n → Bool, gateVal n C g x = true ∧ graphFun G ∅ x = false) :=
    (Finset.mem_filter.mp hgj).2
  obtain ⟨hgop, hglen, x0, hx0, hx0F⟩ := hgj2
  have hg : ¬ Bel n C g := by
    intro hb
    have h1 := hb x0 hx0
    rw [hF, hx0F] at h1
    exact absurd h1 (by simp)
  have hJ : ∀ h, h < C.gates.length → (gateAt C h).op = GateOp.and → ¬ Bel n C h → h = g := by
    intro h hh hhop hnb
    have h1 : h ∈ PEqualNP.TopForm.junk G C := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hh, ?_⟩
      show (gateAt C h).op = GateOp.and ∧ (h < C.gates.length ∧
        ∃ x : Fin n → Bool, gateVal n C h x = true ∧ graphFun G ∅ x = false)
      refine ⟨hhop, hh, ?_⟩
      by_contra hno
      push Not at hno
      apply hnb
      intro x hx
      rw [hF]
      have h2 := hno x hx
      simpa using h2
    rw [hjunk] at h1
    exact Finset.mem_singleton.mp h1
  have hT : ∀ h j, j < C.gates.length → (gateAt C j).op = GateOp.and → InCone n C h j →
      (gateAt C h).op = GateOp.and → ¬ Bel n C h := by
    intro h j hj hjop hc hhop hb
    have hlt := inCone_lt n C j hj h hc
    exact hTop h (by omega) j hj hhop (fun x hx => by rw [← hF]; exact hb x hx) hjop hc
  have hmix1 : m ∈ PEqualNP.TopForm.orN G C := (Finset.mem_filter.mp hmix).1
  simp only [PEqualNP.TopForm.orN, PEqualNP.TopForm.gatesWhere, Finset.mem_filter,
    Finset.mem_range] at hmix1
  have hm : m < C.gates.length := hmix1.1
  have hmop : (gateAt C m).op = GateOp.or := hmix1.2.1
  obtain ⟨h1, h2⟩ := main_abs n G C hL hF hE g m y hT hJ hg hm hmop hgm hy hyg
  refine ⟨?_, ?_⟩
  · obtain ⟨u, hu1, hu2⟩ := h1
    exact ⟨u, (orIn_iff n C hA y u).mpr hu1, hu2⟩
  · intro u hu a ha t hreach
    simp only [PEqualNP.TopForm.tops, PEqualNP.TopForm.gatesWhere, Finset.mem_filter,
      Finset.mem_range] at ha
    have halen : a < C.gates.length := ha.1
    have haop : (gateAt C a).op = GateOp.and := ha.2.1
    have habel : ∀ x : Fin n → Bool, gateVal n C a x = true → graphFun G ∅ x = true := ha.2.2
    obtain ⟨_, a1, b1, hab, ha1, hb1⟩ := hA a halen
    have ho0 : PEqualNP.TopForm.opnd C a 0 = a1 := by simp [PEqualNP.TopForm.opnd, hab]
    have ho1 : PEqualNP.TopForm.opnd C a 1 = b1 := by simp [PEqualNP.TopForm.opnd, hab]
    have hab' : (gateAt C a).inputs =
        [PEqualNP.TopForm.opnd C a 0, PEqualNP.TopForm.opnd C a 1] := by
      rw [ho0, ho1]
      exact hab
    have hs : ∀ (s : Fin 2) (z : Fin n), z ∈ PEqualNP.TopForm.side (n := n) C a s ↔
        OrR n C (PEqualNP.TopForm.opnd C a s) z.val := fun s z => orIn_iff n C hA _ z
    have huy := (orIn_iff n C hA y u).mp hu
    rcases fin2_cases t with ⟨rfl, ht⟩ | ⟨rfl, ht⟩
    · rw [ht]
      have hpm := ((orReaches_iff n C hA _ m).mp hreach).2.2
      obtain ⟨k1, k2, k3⟩ := h2 u huy a (PEqualNP.TopForm.opnd C a 0)
        (PEqualNP.TopForm.opnd C a 1) halen haop (Or.inl hab') habel hpm
      refine ⟨(hs 0 u).mpr k1, ?_, ?_⟩
      · intro v w _ hvw hnot
        obtain ⟨k4, z, hz1, hz2⟩ := k3 v w hvw (fun v' w' hv' hw' =>
          not_cross _ _ v w hnot v' w' (Or.inl ⟨(hs 0 v').mpr hv', (hs 1 w').mpr hw'⟩))
        obtain ⟨k5, k6⟩ := k2 z hz1
        exact ⟨k4, z, mem_wmax G C g z k6, k5, hz2⟩
      · intro _ z hz
        obtain ⟨_, k6⟩ := k2 z ((hs 1 z).mp hz)
        exact mem_wmax G C g z k6
    · rw [ht]
      have hpm := ((orReaches_iff n C hA _ m).mp hreach).2.2
      obtain ⟨k1, k2, k3⟩ := h2 u huy a (PEqualNP.TopForm.opnd C a 1)
        (PEqualNP.TopForm.opnd C a 0) halen haop (Or.inr hab') habel hpm
      refine ⟨(hs 1 u).mpr k1, ?_, ?_⟩
      · intro v w _ hvw hnot
        obtain ⟨k4, z, hz1, hz2⟩ := k3 v w hvw (fun v' w' hv' hw' =>
          not_cross _ _ v w hnot v' w' (Or.inr ⟨(hs 1 v').mpr hv', (hs 0 w').mpr hw'⟩))
        obtain ⟨k5, k6⟩ := k2 z hz1
        exact ⟨k4, z, mem_wmax G C g z k6, k5, hz2⟩
      · intro _ z hz
        obtain ⟨_, k6⟩ := k2 z ((hs 0 z).mp hz)
        exact mem_wmax G C g z k6
end M1506
theorem thm_1506 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
  PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C →
  PEqualNP.TopForm.TopForm G C → ∀ (g : ℕ), PEqualNP.TopForm.junk G C = {g} →
    ∀ m ∈ PEqualNP.TopForm.mixing G C, n + g ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C m).inputs →
    ∀ y ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C m).inputs, y ≠ n + g →
      (∃ u ∈ PEqualNP.TopForm.orIn n C y,
        PEqualNP.EdgeOwnership.gateVal n C g (PEqualNP.EdgeOwnership.pairInput u u) = false) ∧
      ∀ u ∈ PEqualNP.TopForm.orIn n C y, ∀ a ∈ PEqualNP.TopForm.tops G C, ∀ t : Fin 2,
        PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C a t) m →
          u ∈ PEqualNP.TopForm.side (n := n) C a t ∧
          (∀ v w : Fin n, G.Adj v w →
            PEqualNP.EdgeOwnership.gateVal n C a (PEqualNP.EdgeOwnership.pairInput v w) = true →
            s(v, w) ∉ (PEqualNP.TopForm.side (n := n) C a 0 ×ˢ PEqualNP.TopForm.side (n := n) C a 1).image
              (fun p => s(p.1, p.2)) →
            PEqualNP.EdgeOwnership.gateVal n C g (PEqualNP.EdgeOwnership.pairInput v w) = true ∧
            ∃ z ∈ PEqualNP.TopForm.wmax G C g, G.Adj u z ∧ (z = v ∨ z = w)) ∧
          (PEqualNP.TopForm.side (n := n) C a t = {u} →
            PEqualNP.TopForm.side (n := n) C a (1 - t) ⊆ PEqualNP.TopForm.wmax G C g) := by
  intro n G _ C _ hE hLeast hTop g hjunk m hmix hgm y hy hyg
  exact PEqualNP.Outside.L_meta_2448_aux.foundation.M1506.final n G C hE hLeast hTop g hjunk m hmix hgm y hy hyg

namespace M1529
theorem main_aux : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], PEqualNP.TopForm.NoFourCycle G → ∀ (P Q W : Finset (Fin n)),
    (∀ w, w ∈ W ↔ ∀ p ∈ P, ∀ q ∈ Q, G.Adj p q ∨ G.Adj p w ∨ G.Adj q w) →
    (∀ w ∈ W, w ∈ P → w ∉ Q ∧ ∀ q ∈ Q, G.Adj w q) ∧
    (∀ w ∈ W, w ∈ Q → w ∉ P ∧ ∀ p ∈ P, G.Adj w p) ∧
    (∀ s ∈ P ∩ Q, ∀ w ∈ W, G.Adj s w) ∧ (∀ s ∈ P ∩ Q, s ∉ W) ∧
    (2 ≤ (P ∩ Q).card → W.card ≤ 1) := by
  intro n G _ hG P Q W hW
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro w hw hwP
    have h := (hW w).1 hw
    refine ⟨?_, ?_⟩
    · intro hwQ
      rcases h w hwP w hwQ with h1 | h1 | h1 <;> exact G.irrefl h1
    · intro q hq
      rcases h w hwP q hq with h1 | h1 | h1
      · exact h1
      · exact absurd h1 G.irrefl
      · exact h1.symm
  · intro w hw hwQ
    have h := (hW w).1 hw
    refine ⟨?_, ?_⟩
    · intro hwP
      rcases h w hwP w hwQ with h1 | h1 | h1 <;> exact G.irrefl h1
    · intro p hp
      rcases h p hp w hwQ with h1 | h1 | h1
      · exact h1.symm
      · exact h1.symm
      · exact absurd h1 G.irrefl
  · intro s hs w hw
    have hsP := (Finset.mem_inter.1 hs).1
    have hsQ := (Finset.mem_inter.1 hs).2
    rcases (hW w).1 hw s hsP s hsQ with h1 | h1 | h1
    · exact absurd h1 G.irrefl
    · exact h1
    · exact h1
  · intro s hs hsW
    have hsP := (Finset.mem_inter.1 hs).1
    have hsQ := (Finset.mem_inter.1 hs).2
    rcases (hW s).1 hsW s hsP s hsQ with h1 | h1 | h1 <;> exact G.irrefl h1
  · intro h2
    obtain ⟨s, hs, t, ht, hst⟩ := Finset.one_lt_card.1 h2
    have key : ∀ u ∈ P ∩ Q, ∀ w ∈ W, G.Adj u w := by
      intro u hu w hw
      have huP := (Finset.mem_inter.1 hu).1
      have huQ := (Finset.mem_inter.1 hu).2
      rcases (hW w).1 hw u huP u huQ with h1 | h1 | h1
      · exact absurd h1 G.irrefl
      · exact h1
      · exact h1
    refine le_trans (Finset.card_le_card ?_) (hG s t hst)
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨key s hs w hw, key t ht w hw⟩
end M1529
theorem thm_1529 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], PEqualNP.TopForm.NoFourCycle G → ∀ (P Q W : Finset (Fin n)),
    (∀ w, w ∈ W ↔ ∀ p ∈ P, ∀ q ∈ Q, G.Adj p q ∨ G.Adj p w ∨ G.Adj q w) →
    (∀ w ∈ W, w ∈ P → w ∉ Q ∧ ∀ q ∈ Q, G.Adj w q) ∧
    (∀ w ∈ W, w ∈ Q → w ∉ P ∧ ∀ p ∈ P, G.Adj w p) ∧
    (∀ s ∈ P ∩ Q, ∀ w ∈ W, G.Adj s w) ∧ (∀ s ∈ P ∩ Q, s ∉ W) ∧
    (2 ≤ (P ∩ Q).card → W.card ≤ 1) :=
  PEqualNP.Outside.L_meta_2448_aux.foundation.M1529.main_aux

namespace M1530
theorem core (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hno : ∀ s t w w' : Fin n, s ≠ t → w ≠ w' → G.Adj s w → G.Adj t w → G.Adj s w' →
      G.Adj t w' → False)
    (P Q W : Finset (Fin n))
    (hW : ∀ w, w ∈ W ↔ ∀ p ∈ P, ∀ q ∈ Q, G.Adj p q ∨ G.Adj p w ∨ G.Adj q w) :
    (2 ≤ Q.card → (W ∩ P).card ≤ 1) ∧ (2 ≤ P.card → (W ∩ Q).card ≤ 1) ∧
    (∀ a b : Fin n, G.Adj a b → (a ∈ P ∨ b ∈ P) → (a ∈ Q ∨ b ∈ Q) → a ∈ W →
      (a ∈ P → b ∈ Q) ∧ (a ∈ Q → b ∈ P) ∧ (a ∉ P → a ∉ Q → b ∈ P ∩ Q)) ∧
    (∀ s, P ∩ Q = {s} → ∀ u, u ≠ s → ((Finset.univ.filter fun w => G.Adj u w) ∩ W).card ≤ 1) := by
  have kP : ∀ w ∈ W, w ∈ P → ∀ q ∈ Q, G.Adj w q := by
    intro w hw hwP q hq
    rcases (hW w).1 hw w hwP q hq with h | h | h
    · exact h
    · exact absurd h (G.loopless.irrefl w)
    · exact h.symm
  have kQ : ∀ w ∈ W, w ∈ Q → ∀ p ∈ P, G.Adj w p := by
    intro w hw hwQ p hp
    rcases (hW w).1 hw p hp w hwQ with h | h | h
    · exact h.symm
    · exact h.symm
    · exact absurd h (G.loopless.irrefl w)
  have h3 : ∀ s ∈ P ∩ Q, ∀ w ∈ W, G.Adj s w := by
    intro s hs w hw
    obtain ⟨hsP, hsQ⟩ := Finset.mem_inter.1 hs
    rcases (hW w).1 hw s hsP s hsQ with h | h | h
    · exact absurd h (G.loopless.irrefl s)
    · exact h
    · exact h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h2
    obtain ⟨q, hq, q', hq', hqq⟩ := Finset.one_lt_card.1 h2
    apply Finset.card_le_one.2
    intro w hw w' hw'
    rw [Finset.mem_inter] at hw hw'
    by_contra hne
    exact hno w w' q q' hne hqq (kP w hw.1 hw.2 q hq) (kP w' hw'.1 hw'.2 q hq)
      (kP w hw.1 hw.2 q' hq') (kP w' hw'.1 hw'.2 q' hq')
  · intro h2
    obtain ⟨p, hp, p', hp', hpp⟩ := Finset.one_lt_card.1 h2
    apply Finset.card_le_one.2
    intro w hw w' hw'
    rw [Finset.mem_inter] at hw hw'
    by_contra hne
    exact hno w w' p p' hne hpp (kQ w hw.1 hw.2 p hp) (kQ w' hw'.1 hw'.2 p hp)
      (kQ w hw.1 hw.2 p' hp') (kQ w' hw'.1 hw'.2 p' hp')
  · intro a b _ hP hQ haW
    have nPQ : a ∈ P → a ∉ Q := fun haP haQ => G.loopless.irrefl a (kP a haW haP a haQ)
    refine ⟨fun haP => ?_, fun haQ => ?_, fun haP haQ => ?_⟩
    · rcases hQ with h | h
      · exact absurd h (nPQ haP)
      · exact h
    · rcases hP with h | h
      · exact absurd haQ (nPQ h)
      · exact h
    · rcases hP with h | h
      · exact absurd h haP
      · rcases hQ with h' | h'
        · exact absurd h' haQ
        · exact Finset.mem_inter.2 ⟨h, h'⟩
  · intro s hs u hus
    have hsm : s ∈ P ∩ Q := by rw [hs]; simp
    apply Finset.card_le_one.2
    intro w hw w' hw'
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hw hw'
    by_contra hne
    exact hno s u w w' (Ne.symm hus) hne (h3 s hsm w hw.2) hw.1 (h3 s hsm w' hw'.2) hw'.1
end M1530
theorem thm_1530 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], PEqualNP.TopForm.NoFourCycle G → ∀ (P Q W : Finset (Fin n)),
    (∀ w, w ∈ W ↔ ∀ p ∈ P, ∀ q ∈ Q, G.Adj p q ∨ G.Adj p w ∨ G.Adj q w) →
    (2 ≤ Q.card → (W ∩ P).card ≤ 1) ∧ (2 ≤ P.card → (W ∩ Q).card ≤ 1) ∧
    (∀ a b : Fin n, G.Adj a b → (a ∈ P ∨ b ∈ P) → (a ∈ Q ∨ b ∈ Q) → a ∈ W →
      (a ∈ P → b ∈ Q) ∧ (a ∈ Q → b ∈ P) ∧ (a ∉ P → a ∉ Q → b ∈ P ∩ Q)) ∧
    (∀ s, P ∩ Q = {s} → ∀ u, u ≠ s → ((Finset.univ.filter fun w => G.Adj u w) ∩ W).card ≤ 1) := by
  intro n G _ hnf P Q W hW
  have hno : ∀ s t w w' : Fin n, s ≠ t → w ≠ w' → G.Adj s w → G.Adj t w → G.Adj s w' →
      G.Adj t w' → False := by
    intro s t w w' hst hww h1 h2 h3 h4
    exact hww (Finset.card_le_one.1 (hnf s t hst) w (by simp [h1, h2]) w' (by simp [h3, h4]))
  exact PEqualNP.Outside.L_meta_2448_aux.foundation.M1530.core n G hno P Q W hW

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
namespace Close
open M1528.P1.S98 (W AO Least Bel aliasWire aliasGate eraseC erase_length erase_AO
  erase_wires erase_W_lt erase_gateAt_lt erase_gateAt_ge W_gate W_input W_or W_and
  gateAt_eq AO_of_IsAO2 IsAO2_of_AO prefix_W)
open M1528.P2 (OrStep OrR Leaf orStep_lt orR_le orStep_mono orR_mono orR_leaf_true orR_leaf
  orR_cone pairInput_true graphFun_pair orReaches_orR orR_orReaches mem_orIn opnd_eq nfc)
def orTreeGates (base : ℕ) : List ℕ → List Gate × ℕ
  | [] => ([], 0)
  | [w] => ([], w)
  | w :: ws =>
    let (gs, out) := orTreeGates base ws
    (gs ++ [⟨GateOp.or, [w, out]⟩], base + gs.length)
lemma orTreeGates_length (base : ℕ) (ws : List ℕ) (hne : ws ≠ []) :
    (orTreeGates base ws).1.length + 1 = ws.length := by
  induction ws with
  | nil => contradiction
  | cons w ws ih =>
    cases ws with
    | nil => simp [orTreeGates]
    | cons w2 ws2 =>
      have h := ih (by simp)
      simp only [orTreeGates, List.length_append, List.length_cons, List.length_nil] at h ⊢
      omega
lemma orTreeGates_out_lt (base : ℕ) (ws : List ℕ) (hne : ws ≠ [])
    (hws : ∀ w ∈ ws, w < base) :
    (orTreeGates base ws).2 < base + (orTreeGates base ws).1.length := by
  induction ws with
  | nil => contradiction
  | cons w ws ih =>
    cases ws with
    | nil =>
      simp only [orTreeGates, List.length_nil, add_zero]
      exact hws w (by simp)
    | cons w2 ws2 =>
      simp only [orTreeGates, List.length_append, List.length_singleton]
      omega
lemma orTreeGates_eval (n : ℕ) (pre : List Gate) (ws : List ℕ) (hne : ws ≠ [])
    (hws : ∀ w ∈ ws, w < n + pre.length) (x : Fin n → Bool) :
    let res := orTreeGates (n + pre.length) ws
    let C' : Circuit := ⟨pre ++ res.1, res.2⟩
    (∀ k (hk : k < res.1.length),
      let g := res.1[k]'hk
      (g.op = GateOp.or) ∧ ∃ a b, g.inputs = [a, b] ∧ a < n + pre.length + k ∧ b < n + pre.length + k) ∧
    (W n C' x res.2 = true ↔ ∃ w ∈ ws, W n ⟨pre, 0⟩ x w = true) := by
  induction ws with
  | nil => contradiction
  | cons w ws ih =>
    cases ws with
    | nil =>
      simp only [orTreeGates, List.append_nil]
      refine ⟨fun k hk => by simp at hk, ?_⟩
      simp only [List.mem_singleton, exists_eq_left]
      have hpre : W n ⟨pre, w⟩ x w = W n ⟨pre, 0⟩ x w := by
        simp [W, Circuit.wires]
      rw [hpre]
    | cons w2 ws2 =>
      have hne' : w2 :: ws2 ≠ [] := by simp
      have hws' : ∀ u ∈ w2 :: ws2, u < n + pre.length := fun u hu => hws u (by simp [hu])
      have hw : w < n + pre.length := hws w (by simp)
      obtain ⟨hAO', heval'⟩ := ih hne' hws'
      set gs := (orTreeGates (n + pre.length) (w2 :: ws2)).1
      set out := (orTreeGates (n + pre.length) (w2 :: ws2)).2
      have hout_lt : out < n + pre.length + gs.length :=
        orTreeGates_out_lt (n + pre.length) (w2 :: ws2) hne' hws'
      have hres_eq : orTreeGates (n + pre.length) (w :: w2 :: ws2) =
          (gs ++ [⟨GateOp.or, [w, out]⟩], n + pre.length + gs.length) := rfl
      dsimp only
      rw [hres_eq]
      constructor
      · intro k hk
        have hk' : k < gs.length + 1 := by simpa [List.length_append] using hk
        by_cases hkl : k < gs.length
        · have hget : (gs ++ [⟨GateOp.or, [w, out]⟩])[k]'hk = gs[k]'hkl :=
            List.getElem_append_left hkl
          rw [hget]
          exact hAO' k hkl
        · have hkeq : k = gs.length := by omega
          subst hkeq
          have hget : (gs ++ [⟨GateOp.or, [w, out]⟩])[gs.length]'hk = ⟨GateOp.or, [w, out]⟩ := by
            simp
          rw [hget]
          exact ⟨rfl, w, out, rfl, by omega, by omega⟩
      · let C1 : Circuit := ⟨pre ++ gs, out⟩
        let C2 : Circuit := ⟨pre ++ (gs ++ [⟨GateOp.or, [w, out]⟩]), n + pre.length + gs.length⟩
        change W n C2 x (n + pre.length + gs.length) = true ↔ _
        have hlen : C2.gates.length = pre.length + gs.length + 1 := by simp [C2]; omega
        have hidx : pre.length + gs.length < C2.gates.length := by omega
        have hgate : gateAt C2 (pre.length + gs.length) = ⟨GateOp.or, [w, out]⟩ := by
          rw [gateAt_eq C2 (pre.length + gs.length) hidx]
          simp [C2, ← List.append_assoc]
        have hWlast : W n C2 x (n + (pre.length + gs.length)) =
            (W n C2 x w || W n C2 x out) := by
          exact W_or n C2 x (pre.length + gs.length) hidx (by rw [hgate]) w out (by rw [hgate])
            (by omega) (by omega)
        have hCw : W n C2 x w = W n ⟨pre, 0⟩ x w := by
          have := prefix_W n pre (gs ++ [⟨GateOp.or, [w, out]⟩]) []
            (n + pre.length + gs.length) 0 x w hw
          simpa [C2] using this
        have hCout : W n C2 x out = W n C1 x out := by
          have h2 : C2 = ⟨(pre ++ gs) ++ [⟨GateOp.or, [w, out]⟩], n + pre.length + gs.length⟩ := by
            simp [C2, List.append_assoc]
          have h1 : C1 = ⟨(pre ++ gs) ++ [], out⟩ := by simp [C1]
          rw [h2, h1]
          exact prefix_W n (pre ++ gs) [⟨GateOp.or, [w, out]⟩] []
            (n + pre.length + gs.length) out x out (by simp; omega)
        have hadd : n + pre.length + gs.length = n + (pre.length + gs.length) := by omega
        rw [hadd, hWlast, hCw, hCout, Bool.or_eq_true, heval']
        simp
def OrStepOut (n : ℕ) (C : Circuit) (B : Finset ℕ) (u v : ℕ) : Prop :=
  ∃ k, u = n + k ∧ k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧ k ∉ B ∧
    v ∈ (gateAt C k).inputs
def OrROut (n : ℕ) (C : Circuit) (B : Finset ℕ) : ℕ → ℕ → Prop :=
  Relation.ReflTransGen (OrStepOut n C B)
lemma orROut_to_orR {n : ℕ} {C : Circuit} {B : Finset ℕ} {u v : ℕ}
    (h : OrROut n C B u v) : OrR n C u v := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ h2 ih =>
    obtain ⟨k, rfl, hk, hop, _, hin⟩ := h2
    exact Relation.ReflTransGen.tail ih ⟨k, rfl, hk, hop, hin⟩
lemma orStepOut_lt {n : ℕ} {C : Circuit} (hA : AO n C) {B : Finset ℕ} {u v : ℕ}
    (h : OrStepOut n C B u v) : v < u := by
  obtain ⟨k, rfl, hk, hop, _, hin⟩ := h
  exact orStep_lt n C hA (n + k) v ⟨k, rfl, hk, hop, hin⟩
lemma orROut_le {n : ℕ} {C : Circuit} (hA : AO n C) {B : Finset ℕ} {u v : ℕ}
    (h : OrROut n C B u v) : v ≤ u :=
  orR_le n C hA u v (orROut_to_orR h)
open Classical in
theorem or_dag_leaf_bound {n : ℕ} (C : Circuit) (hA : AO n C)
    (T : Finset (Fin n)) (B : Finset ℕ)
    (hB : ∀ h ∈ B, ((orIn n C (n + h)) ∩ T).card ≤ 1)
    (R : Finset ℕ)
    (hR_lt : ∀ w ∈ R, w < n + C.gates.length)
    (hnoAnd : ∀ w ∈ R, ∀ h, h < C.gates.length → (gateAt C h).op = GateOp.and → ¬ OrR n C w (n + h)) :
    let F := (Finset.range C.gates.length).filter fun h =>
      (gateAt C h).op = GateOp.or ∧ h ∉ B ∧ ∃ w ∈ R, OrR n C w (n + h)
    ((R.biUnion fun w => orIn n C w) ∩ T).card ≤ R.card + F.card := by
  classical
  intro F
  let Fout : Finset ℕ → Finset ℕ := fun R0 =>
    (Finset.range C.gates.length).filter fun h =>
      (gateAt C h).op = GateOp.or ∧ h ∉ B ∧ ∃ w ∈ R0, OrROut n C B w (n + h)
  have hFout_sub : Fout R ⊆ F := by
    intro h hh
    simp only [Fout, F, Finset.mem_filter] at hh ⊢
    obtain ⟨hrng, hop, hnotB, w, hwR, hr⟩ := hh
    exact ⟨hrng, hop, hnotB, w, hwR, orROut_to_orR hr⟩
  suffices hmain : ∀ m : ℕ, ∀ R0 : Finset ℕ,
      (∀ w ∈ R0, w < n + C.gates.length) →
      (∀ w ∈ R0, ∀ h, h < C.gates.length → (gateAt C h).op = GateOp.and → ¬ OrR n C w (n + h)) →
      (Fout R0).card = m →
      ((R0.biUnion fun w => orIn n C w) ∩ T).card ≤ R0.card + m by
    exact (hmain (Fout R).card R hR_lt hnoAnd rfl).trans
      (Nat.add_le_add_left (Finset.card_le_card hFout_sub) R.card)
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro R0 hR0_lt hR0_noAnd hm
    by_cases hFempty : Fout R0 = ∅
    · have hm0 : m = 0 := by rw [← hm, hFempty, Finset.card_empty]
      rw [hm0, add_zero]
      calc ((R0.biUnion fun w => orIn n C w) ∩ T).card
          = (R0.biUnion fun w => (orIn n C w) ∩ T).card := by
              congr 1; ext u; simp only [Finset.mem_inter, Finset.mem_biUnion]; tauto
        _ ≤ ∑ w ∈ R0, ((orIn n C w) ∩ T).card := Finset.card_biUnion_le
        _ ≤ ∑ _w ∈ R0, 1 := by
              refine Finset.sum_le_sum fun w hw => ?_
              by_cases hwn : w < n
              · have hsub : (orIn n C w) ∩ T ⊆ {⟨w, hwn⟩} := by
                  intro u hu
                  have hu1 := (mem_orIn n C hA w (hR0_lt w hw) u).mp (Finset.mem_inter.mp hu).1
                  rcases Relation.ReflTransGen.cases_head hu1 with heq | ⟨c, ⟨k, hk, _⟩, _⟩
                  · exact Finset.mem_singleton.mpr (Fin.ext heq.symm)
                  · omega
                exact (Finset.card_le_card hsub).trans (by simp)
              · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
                have hk : k < C.gates.length := by have := hR0_lt (n + k) hw; omega
                rcases (hA k hk).1 with hop | hop
                · exact absurd Relation.ReflTransGen.refl (hR0_noAnd (n + k) hw k hk hop)
                · have hkB : k ∈ B := by
                    by_contra hkNotB
                    have : k ∈ Fout R0 := Finset.mem_filter.mpr
                      ⟨Finset.mem_range.mpr hk, hop, hkNotB, n + k, hw, Relation.ReflTransGen.refl⟩
                    rw [hFempty] at this
                    exact Finset.notMem_empty _ this
                  exact hB k hkB
        _ = R0.card := by simp
    · have hFne : (Fout R0).Nonempty := Finset.nonempty_iff_ne_empty.mpr hFempty
      let h := (Fout R0).max' hFne
      have hhF : h ∈ Fout R0 := Finset.max'_mem (Fout R0) hFne
      have hh_lt : h < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hhF).1
      have hh_op : (gateAt C h).op = GateOp.or := (Finset.mem_filter.mp hhF).2.1
      have hh_notB : h ∉ B := (Finset.mem_filter.mp hhF).2.2.1
      obtain ⟨w0, hw0R, hw0_reach⟩ := (Finset.mem_filter.mp hhF).2.2.2
      have hreach_eq : ∀ w ∈ R0, OrROut n C B w (n + h) → w = n + h := by
        intro w hw hr
        rcases Relation.ReflTransGen.cases_head hr with heq | ⟨c, hstep, hrest⟩
        · exact heq
        · obtain ⟨k, rfl, hk, hkop, hkB, hkin⟩ := hstep
          have hlt1 := orStepOut_lt hA ⟨k, rfl, hk, hkop, hkB, hkin⟩
          have hle2 := orROut_le hA hrest
          have hkF : k ∈ Fout R0 := Finset.mem_filter.mpr
            ⟨Finset.mem_range.mpr hk, hkop, hkB, n + k, hw, Relation.ReflTransGen.refl⟩
          have hk_le : k ≤ h := Finset.le_max' (Fout R0) k hkF
          omega
      have hhR : n + h ∈ R0 := by
        have := hreach_eq w0 hw0R hw0_reach
        rwa [← this]
      obtain ⟨_, a, b, hab, ha_lt, hb_lt⟩ := hA h hh_lt
      let R' := (R0.erase (n + h)) ∪ {a, b}
      have hstep_a : OrStep n C (n + h) a := ⟨h, rfl, hh_lt, hh_op, by rw [hab]; simp⟩
      have hstep_b : OrStep n C (n + h) b := ⟨h, rfl, hh_lt, hh_op, by rw [hab]; simp⟩
      have hstepOut_a : OrStepOut n C B (n + h) a :=
        ⟨h, rfl, hh_lt, hh_op, hh_notB, by rw [hab]; simp⟩
      have hstepOut_b : OrStepOut n C B (n + h) b :=
        ⟨h, rfl, hh_lt, hh_op, hh_notB, by rw [hab]; simp⟩
      have hR'_lt : ∀ w ∈ R', w < n + C.gates.length := by
        intro w hw
        simp only [R', Finset.mem_union, Finset.mem_erase, Finset.mem_insert,
          Finset.mem_singleton] at hw
        rcases hw with ⟨_, hwR⟩ | rfl | rfl
        · exact hR0_lt w hwR
        · omega
        · omega
      have hR'_noAnd : ∀ w ∈ R', ∀ k, k < C.gates.length → (gateAt C k).op = GateOp.and →
          ¬ OrR n C w (n + k) := by
        intro w hw k hk hop hr
        simp only [R', Finset.mem_union, Finset.mem_erase, Finset.mem_insert,
          Finset.mem_singleton] at hw
        rcases hw with ⟨_, hwR⟩ | rfl | rfl
        · exact hR0_noAnd w hwR k hk hop hr
        · exact hR0_noAnd (n + h) hhR k hk hop (Relation.ReflTransGen.head hstep_a hr)
        · exact hR0_noAnd (n + h) hhR k hk hop (Relation.ReflTransGen.head hstep_b hr)
      have hF'_sub : Fout R' ⊆ (Fout R0).erase h := by
        intro k hk
        simp only [Fout, Finset.mem_filter] at hk
        obtain ⟨hkrng, hkop, hkB, w, hwR', hwk⟩ := hk
        have hwk_orig : ∃ w' ∈ R0, OrROut n C B w' (n + k) := by
          simp only [R', Finset.mem_union, Finset.mem_erase, Finset.mem_insert,
            Finset.mem_singleton] at hwR'
          rcases hwR' with ⟨_, hwR⟩ | rfl | rfl
          · exact ⟨w, hwR, hwk⟩
          · exact ⟨n + h, hhR, Relation.ReflTransGen.head hstepOut_a hwk⟩
          · exact ⟨n + h, hhR, Relation.ReflTransGen.head hstepOut_b hwk⟩
        have hkF0 : k ∈ Fout R0 := Finset.mem_filter.mpr ⟨hkrng, hkop, hkB, hwk_orig⟩
        refine Finset.mem_erase.mpr ⟨?_, hkF0⟩
        intro hkh
        subst hkh
        simp only [R', Finset.mem_union, Finset.mem_erase, Finset.mem_insert,
          Finset.mem_singleton] at hwR'
        rcases hwR' with ⟨hne, hwR⟩ | rfl | rfl
        · exact hne (hreach_eq w hwR hwk)
        · have := orROut_le hA hwk; omega
        · have := orROut_le hA hwk; omega
      have hF'_lt : (Fout R').card < m := by
        have h1 : (Fout R').card ≤ ((Fout R0).erase h).card := Finset.card_le_card hF'_sub
        have h2 : ((Fout R0).erase h).card + 1 = (Fout R0).card := Finset.card_erase_add_one hhF
        omega
      have hR'_card : R'.card ≤ R0.card + 1 := by
        have h1 : R'.card ≤ (R0.erase (n + h)).card + ({a, b} : Finset ℕ).card :=
          Finset.card_union_le _ _
        have h2 : ({a, b} : Finset ℕ).card ≤ 2 := Finset.card_le_two
        have h3 : (R0.erase (n + h)).card + 1 = R0.card := Finset.card_erase_add_one hhR
        omega
      have hunion_sub : R0.biUnion (fun w => orIn n C w) ⊆ R'.biUnion (fun w => orIn n C w) := by
        intro u hu
        simp only [Finset.mem_biUnion] at hu ⊢
        obtain ⟨w, hwR, huw⟩ := hu
        by_cases hwh : w = n + h
        · subst hwh
          have hr := (mem_orIn n C hA (n + h) (by omega) u).mp huw
          rcases Relation.ReflTransGen.cases_head hr with heq | ⟨c, hst, hrest⟩
          · have := u.isLt; omega
          · obtain ⟨k, hk_eq, _, _, hc⟩ := hst
            have hkh : k = h := by omega
            subst hkh
            rw [hab] at hc
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
            rcases hc with rfl | rfl
            · exact ⟨c, Finset.mem_union_right _ (by simp),
                (mem_orIn n C hA c (by omega) u).mpr hrest⟩
            · exact ⟨c, Finset.mem_union_right _ (by simp),
                (mem_orIn n C hA c (by omega) u).mpr hrest⟩
        · exact ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwh, hwR⟩), huw⟩
      have hih := ih (Fout R').card hF'_lt R' hR'_lt hR'_noAnd rfl
      have hsub_card : ((R0.biUnion fun w => orIn n C w) ∩ T).card ≤
          ((R'.biUnion fun w => orIn n C w) ∩ T).card :=
        Finset.card_le_card (Finset.inter_subset_inter_right hunion_sub)
      omega
lemma opnd_lt' {n : ℕ} {C : Circuit} (hA : AO n C) (a : ℕ) (ha : a < C.gates.length) (b : Fin 2) :
    opnd C a b < n + a :=
  M1528.P2.opnd_lt n C hA a ha (opnd C a) (opnd_eq n C hA a ha) b
lemma W_eq_gateVal {n : ℕ} (C : Circuit) (k : ℕ) (x : Fin n → Bool) :
    W n C x (n + k) = gateVal n C k x := rfl
lemma W_mono_input {n : ℕ} (C : Circuit) (hA : AO n C) (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true) :
    ∀ u, u < n + C.gates.length → W n C x u = true → W n C y u = true := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu hx
    by_cases h1 : u < n
    · rw [W_input n C x u h1] at hx
      rw [W_input n C y u h1]
      exact hxy ⟨u, h1⟩ hx
    · obtain ⟨k, rfl⟩ : ∃ k, u = n + k := ⟨u - n, by omega⟩
      have hk : k < C.gates.length := by omega
      obtain ⟨hop, a, b, hab, ha, hb⟩ := hA k hk
      rcases hop with hop | hop
      · rw [W_and n C x k hk hop a b hab ha hb, Bool.and_eq_true] at hx
        rw [W_and n C y k hk hop a b hab ha hb, Bool.and_eq_true]
        exact ⟨ih a ha (by omega) hx.1, ih b hb (by omega) hx.2⟩
      · rw [W_or n C x k hk hop a b hab ha hb, Bool.or_eq_true] at hx
        rw [W_or n C y k hk hop a b hab ha hb, Bool.or_eq_true]
        rcases hx with hx | hx
        · exact Or.inl (ih a ha (by omega) hx)
        · exact Or.inr (ih b hb (by omega) hx)
lemma least_of_isLeastAO {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) : Least n C := by
  refine ⟨AO_of_IsAO2 n C hL.1, fun D hAD hDeq => ?_⟩
  have hfun : circuitFun n D = graphFun G ∅ := by
    funext x
    rw [← hL.2.1]
    exact hDeq x
  exact hL.2.2 D (IsAO2_of_AO n D hAD) hfun
lemma graphFun_single_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u : Fin n) : graphFun G ∅ (pairInput u u) = false := by
  rw [Bool.eq_false_iff, ne_eq, graphFun_pair]
  exact G.irrefl
lemma junk_single_props {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g}) :
    g < C.gates.length ∧ (gateAt C g).op = GateOp.and ∧ ¬ BelowF G C g ∧
    (∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ¬ BelowF G C k → k = g) ∧
    (∀ h < C.gates.length, (gateAt C h).op = GateOp.and → InCone n C h g → False) ∧
    (∀ a ∈ tops G C, ∀ h < C.gates.length, (gateAt C h).op = GateOp.and → InCone n C h a → h = g) := by
  have hA : AO n C := AO_of_IsAO2 n C hL.1
  have hmem_iff : ∀ k, k ∈ junk G C ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧ ¬ BelowF G C k := by
    intro k
    have h1 := M1528.P1.junk_iff G C k
    simpa [BelowF] using h1
  have hgmem : g ∈ junk G C := by rw [hg]; simp
  obtain ⟨hg_lt, hg_op, hg_notB⟩ := (hmem_iff g).mp hgmem
  have huniq : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ¬ BelowF G C k → k = g := by
    intro k hk hop hnotB
    have : k ∈ junk G C := (hmem_iff k).mpr ⟨hk, hop, hnotB⟩
    rw [hg, Finset.mem_singleton] at this
    exact this
  have hno_in_g : ∀ h < C.gates.length, (gateAt C h).op = GateOp.and → InCone n C h g → False := by
    intro h hh hop hc
    by_cases hB : BelowF G C h
    · exact hT h hh g hg_lt hop hB hg_op hc
    · have heq := huniq h hh hop hB
      subst heq
      have hlt : ∀ i k, k < C.gates.length → InCone n C i k → i < k := by
        intro i k
        induction k using Nat.strong_induction_on with
        | _ k ihk =>
          intro hk hic
          rw [M1528.P2.inCone_iff n C i k hk] at hic
          obtain ⟨w, hwin, hnw, hwlt, hcase⟩ := hic
          rcases hcase with rfl | hc'
          · omega
          · have hlt' := ihk (w - n) (by omega) (by omega) hc'
            omega
      exact Nat.lt_irrefl h (hlt h h hg_lt hc)
  have htop_cone : ∀ a ∈ tops G C, ∀ h < C.gates.length, (gateAt C h).op = GateOp.and →
      InCone n C h a → h = g := by
    intro a ha h hh hop hc
    simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha
    by_cases hB : BelowF G C h
    · exact absurd hc (hT h hh a ha.1 hop hB ha.2.1)
    · exact huniq h hh hop hB
  exact ⟨hg_lt, hg_op, hg_notB, huniq, hno_in_g, htop_cone⟩
lemma no_and_in_g_opnd {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g})
    (b : Fin 2) :
    opnd C g b < n + g ∧
    ∀ h < C.gates.length, (gateAt C h).op = GateOp.and → ¬ OrR n C (opnd C g b) (n + h) := by
  have hA : AO n C := AO_of_IsAO2 n C hL.1
  obtain ⟨hg_lt, hg_op, _, _, hno_in_g, _⟩ := junk_single_props G C hL hT g hg
  have hlt := opnd_lt' hA g hg_lt b
  refine ⟨hlt, fun h hh hop hr => ?_⟩
  have hmem : opnd C g b ∈ (gateAt C g).inputs := by
    have := M1528.P2.opnd_eq n C hA g hg_lt
    fin_cases b <;> rw [this] <;> simp
  have hic : InCone n C h g := by
    by_cases hw : opnd C g b < n
    · have := orR_le n C hA _ _ hr; omega
    · obtain ⟨k, hk_eq⟩ : ∃ k, opnd C g b = n + k := ⟨opnd C g b - n, by omega⟩
      rcases orR_cone n C hA h (opnd C g b) hr k hk_eq (by omega) with rfl | hc
      · exact M1528.P2.inCone_c1 n C hA h g hg_lt (hk_eq ▸ hmem)
      · exact M1528.P2.inCone_c2 n C hA h k g hg_lt hc (hk_eq ▸ hmem)
  exact hno_in_g h hh hop hic
lemma pure_or_wire_eval {n : ℕ} (C : Circuit) (hA : AO n C) (w : ℕ) (hw : w < n + C.gates.length)
    (hnoAnd : ∀ h < C.gates.length, (gateAt C h).op = GateOp.and → ¬ OrR n C w (n + h)) :
    (orIn n C w).Nonempty ∧
    ∀ x : Fin n → Bool, W n C x w = true ↔ ∃ u ∈ orIn n C w, x u = true := by
  constructor
  · obtain ⟨v, hrv, hleaf⟩ := orR_leaf n C hA w hw
    rcases hleaf with hvn | ⟨h, rfl, hh, hop⟩
    · exact ⟨⟨v, hvn⟩, (mem_orIn n C hA w hw ⟨v, hvn⟩).mpr hrv⟩
    · exact absurd hrv (hnoAnd h hh hop)
  · intro x
    constructor
    · intro hW
      obtain ⟨v, hrv, hleaf, hWv⟩ := orR_leaf_true n C hA x w hw hW
      rcases hleaf with hvn | ⟨h, rfl, hh, hop⟩
      · rw [M1528.P2.W_input n C x v hvn] at hWv
        exact ⟨⟨v, hvn⟩, (mem_orIn n C hA w hw ⟨v, hvn⟩).mpr hrv, hWv⟩
      · exact absurd hrv (hnoAnd h hh hop)
    · rintro ⟨u, hu, hxu⟩
      have hru := (mem_orIn n C hA w hw u).mp hu
      refine orR_mono n C hA x w u.val hru ?_
      rw [M1528.P2.W_input n C x u.val u.isLt]
      exact hxu
lemma g_semantics {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g}) :
    let P := side (n := n) C g 0
    let Q := side (n := n) C g 1
    let Wg := wmax G C g
    P.Nonempty ∧ Q.Nonempty ∧
    (∀ x : Fin n → Bool, W n C x (n + g) = true ↔
      (∃ p ∈ P, x p = true) ∧ (∃ q ∈ Q, x q = true)) ∧
    (∀ w : Fin n, w ∈ Wg ↔ ∀ p ∈ P, ∀ q ∈ Q, G.Adj p q ∨ G.Adj p w ∨ G.Adj q w) ∧
    (∃ p ∈ P, ∃ q ∈ Q, ¬ G.Adj p q) := by
  have hA : AO n C := AO_of_IsAO2 n C hL.1
  obtain ⟨hg_lt, hg_op, hg_notB, _, _, _⟩ := junk_single_props G C hL hT g hg
  obtain ⟨h0_lt, h0_no⟩ := no_and_in_g_opnd G C hL hT g hg 0
  obtain ⟨h1_lt, h1_no⟩ := no_and_in_g_opnd G C hL hT g hg 1
  obtain ⟨hPne, hPeval⟩ := pure_or_wire_eval C hA (opnd C g 0) (by omega) h0_no
  obtain ⟨hQne, hQeval⟩ := pure_or_wire_eval C hA (opnd C g 1) (by omega) h1_no
  have hgeval : ∀ x : Fin n → Bool, W n C x (n + g) = true ↔
      (∃ p ∈ side (n := n) C g 0, x p = true) ∧ (∃ q ∈ side (n := n) C g 1, x q = true) := by
    intro x
    rw [W_and n C x g hg_lt hg_op (opnd C g 0) (opnd C g 1) (opnd_eq n C hA g hg_lt) h0_lt h1_lt,
      Bool.and_eq_true, hPeval x, hQeval x]
    rfl
  refine ⟨hPne, hQne, hgeval, ?_, ?_⟩
  · intro w
    simp only [wmax, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hw p hp q hq
      let x : Fin n → Bool := fun i => decide (i = p ∨ i = q ∨ i = w)
      have hgx : gateVal n C g x = true := by
        rw [← W_eq_gateVal, hgeval x]
        exact ⟨⟨p, hp, by simp [x]⟩, ⟨q, hq, by simp [x]⟩⟩
      have hxw : x w = true := by simp [x]
      have hF := hw x hgx hxw
      simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
        Bool.false_or, decide_eq_true_eq] at hF
      obtain ⟨a, b, hab, hxa, hxb⟩ := hF
      simp only [x, decide_eq_true_eq] at hxa hxb
      rcases hxa with rfl | rfl | rfl <;> rcases hxb with rfl | rfl | rfl
      · exact (G.irrefl hab).elim
      · exact Or.inl hab
      · exact Or.inr (Or.inl hab)
      · exact Or.inl hab.symm
      · exact (G.irrefl hab).elim
      · exact Or.inr (Or.inr hab)
      · exact Or.inr (Or.inl hab.symm)
      · exact Or.inr (Or.inr hab.symm)
      · exact (G.irrefl hab).elim
    · intro hcond x hgx hxw
      rw [← W_eq_gateVal, hgeval x] at hgx
      obtain ⟨⟨p, hp, hxp⟩, ⟨q, hq, hxq⟩⟩ := hgx
      simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
        Bool.false_or, decide_eq_true_eq]
      rcases hcond p hp q hq with h | h | h
      · exact ⟨p, q, h, hxp, hxq⟩
      · exact ⟨p, w, h, hxp, hxw⟩
      · exact ⟨q, w, h, hxq, hxw⟩
  · simp only [BelowF, not_forall] at hg_notB
    obtain ⟨x, hx⟩ := hg_notB
    push Not at hx
    obtain ⟨hgx, hFx⟩ := hx
    rw [← W_eq_gateVal, hgeval x] at hgx
    obtain ⟨⟨p, hp, hxp⟩, ⟨q, hq, hxq⟩⟩ := hgx
    refine ⟨p, hp, q, hq, fun hadj => hFx ?_⟩
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq]
    exact ⟨p, q, hadj, hxp, hxq⟩
lemma lam_has_center {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (h : ℕ) (hh : h ∈ lam G C) :
    ∃ c : Fin n, ∀ u ∈ orIn n C (n + h), G.Adj c u ∧ s(c, u) ∈ starEdges G C := by
  have hA : AO n C := AO_of_IsAO2 n C hL.1
  simp only [lam, Finset.mem_filter] at hh
  obtain ⟨_, _, _, a, ha, b, hcard1, hreach⟩ := hh
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hcard1
  refine ⟨c, fun u hu => ?_⟩
  simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha
  have hreach_orR := orReaches_orR n C (opnd C a b) (by have := opnd_lt' hA a ha.1 b; omega) h hreach
  have hhu : OrR n C (n + h) u.val := (mem_orIn n C hA (n + h) (by
    have hlt := orR_le n C hA _ _ hreach_orR
    have := opnd_lt' hA a ha.1 b
    omega) u).mp hu
  have hu_side : u ∈ side (n := n) C a b :=
    (mem_orIn n C hA (opnd C a b) (by have := opnd_lt' hA a ha.1 b; omega) u).mpr
      (hreach_orR.trans hhu)
  have hc_side : c ∈ side (n := n) C a (1 - b) := by rw [hc]; simp
  have hadj : G.Adj c u := by
    have hr_c := (mem_orIn n C hA (opnd C a (1 - b))
      (by have := opnd_lt' hA a ha.1 (1 - b); omega) c).mp hc_side
    have hr_u := (mem_orIn n C hA (opnd C a b)
      (by have := opnd_lt' hA a ha.1 b; omega) u).mp hu_side
    have hpair : W n C (pairInput c u) (n + a) = true := by
      have h0 : W n C (pairInput c u) (opnd C a b) = true :=
        orR_mono n C hA _ _ _ hr_u (by rw [M1528.P2.W_input n C _ u.val u.isLt]; simp [pairInput])
      have h1 : W n C (pairInput c u) (opnd C a (1 - b)) = true :=
        orR_mono n C hA _ _ _ hr_c (by rw [M1528.P2.W_input n C _ c.val c.isLt]; simp [pairInput])
      rw [W_and n C _ a ha.1 ha.2.1 (opnd C a 0) (opnd C a 1) (opnd_eq n C hA a ha.1)
        (opnd_lt' hA a ha.1 0) (opnd_lt' hA a ha.1 1), Bool.and_eq_true]
      fin_cases b <;> simp_all
    have hF := ha.2.2 (pairInput c u) hpair
    rwa [graphFun_pair] at hF
  have hstar : s(c, u) ∈ starEdges G C := by
    simp only [starEdges, Finset.mem_biUnion, Finset.mem_image, Finset.mem_product]
    refine ⟨a, by simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range]; exact ha, ?_⟩
    fin_cases b
    · exact ⟨(u, c), ⟨hu_side, by simpa using hc_side⟩, Sym2.eq_swap⟩
    · exact ⟨(c, u), ⟨by simpa using hc_side, hu_side⟩, rfl⟩
  exact ⟨hadj, hstar⟩
lemma lam_card_le_one_of_common_nbr {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (C : Circuit) (hL : IsLeastAO G C)
    (z : Fin n) (T : Finset (Fin n))
    (hadj : ∀ u ∈ T, G.Adj z u)
    (hnotStar : ∀ u v, u ∈ T → v ∈ T → u ≠ v → s(z, u) ∉ starEdges G C ∨ s(z, v) ∉ starEdges G C)
    (h : ℕ) (hh : h ∈ lam G C) :
    ((orIn n C (n + h)) ∩ T).card ≤ 1 := by
  obtain ⟨c, hc⟩ := lam_has_center G C hL h hh
  refine Finset.card_le_one.mpr fun u hu v hv => ?_
  by_contra hne
  have hu1 := (Finset.mem_inter.mp hu).1
  have huT := (Finset.mem_inter.mp hu).2
  have hv1 := (Finset.mem_inter.mp hv).1
  have hvT := (Finset.mem_inter.mp hv).2
  have hcz : c = z := by
    by_contra hcz_ne
    exact nfc n G h4 c u z v hcz_ne hne
      ⟨(hc u hu1).1, (hadj u huT).symm, hadj v hvT, (hc v hv1).1.symm⟩
  subst hcz
  rcases hnotStar u v huT hvT hne with hns | hns
  · exact hns (hc u hu1).2
  · exact hns (hc v hv1).2
lemma pure_or_gate_in_orN_not_mixing {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (w : ℕ) (hw : w < n + C.gates.length)
    (hnoAnd : ∀ h < C.gates.length, (gateAt C h).op = GateOp.and → ¬ OrR n C w (n + h))
    (k : ℕ) (hk : k < C.gates.length) (hkop : (gateAt C k).op = GateOp.or)
    (hr : OrR n C w (n + k)) :
    k ∈ orN G C ∧ k ∉ mixing G C := by
  have hA : AO n C := AO_of_IsAO2 n C hL.1
  have hk_noAnd : ∀ h < C.gates.length, (gateAt C h).op = GateOp.and → ¬ OrR n C (n + k) (n + h) :=
    fun h hh hop hkr => hnoAnd h hh hop (hr.trans hkr)
  have hkne : (orIn n C (n + k)).Nonempty := (pure_or_wire_eval C hA (n + k) (by omega) hk_noAnd).1
  have hnotB : ¬ BelowF G C k := by
    intro hB
    obtain ⟨u, hu⟩ := hkne
    have hWu : W n C (pairInput u u) (n + k) = true :=
      (pure_or_wire_eval C hA (n + k) (by omega) hk_noAnd).2 (pairInput u u) |>.mpr
        ⟨u, hu, by simp [pairInput]⟩
    have hF := hB (pairInput u u) hWu
    rw [graphFun_single_false G u] at hF
    exact Bool.noConfusion hF
  have horN : k ∈ orN G C := by
    simp only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range]
    exact ⟨hk, hkop, hnotB⟩
  have hnotMix : k ∉ mixing G C := by
    simp only [mixing, Finset.mem_filter, not_and]
    intro _
    have hop_ne : ∀ b : Fin 2, (orIn n C (opnd C k b)).Nonempty := by
      intro b
      have hlt := opnd_lt' hA k hk b
      have hmem : opnd C k b ∈ (gateAt C k).inputs := by
        have := opnd_eq n C hA k hk
        fin_cases b <;> rw [this] <;> simp
      have hstep : OrStep n C (n + k) (opnd C k b) := ⟨k, rfl, hk, hkop, hmem⟩
      exact (pure_or_wire_eval C hA (opnd C k b) (by omega) (fun h hh hop hbr =>
        hk_noAnd h hh hop (Relation.ReflTransGen.head hstep hbr))).1
    have h0 := Finset.nonempty_iff_ne_empty.mp (hop_ne 0)
    have h1 := Finset.nonempty_iff_ne_empty.mp (hop_ne 1)
    simp [h0, h1]
  exact ⟨horN, hnotMix⟩
lemma bel_reaches_output {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hE : G.edgeFinset.Nonempty) (hL : IsLeastAO G C) (hT : TopForm G C) :
    (n ≤ C.output ∧ C.output + 1 = n + C.gates.length) ∧
    (∀ j < C.gates.length, BelowF G C j → OrR n C C.output (n + j)) := by
  have hA : AO n C := AO_of_IsAO2 n C hL.1
  have hLeast : Least n C := least_of_isLeastAO G C hL
  have hT_ex : ∃ x : Fin n → Bool, C.eval (List.ofFn x) = true := by
    obtain ⟨e, he⟩ := hE
    induction e using Sym2.ind with
    | _ u v =>
      refine ⟨pairInput u v, ?_⟩
      change circuitFun n C (pairInput u v) = true
      rw [hL.2.1, graphFun_pair]
      exact SimpleGraph.mem_edgeFinset.mp he
  have hV : ∀ u : Fin n, ∃ x : Fin n → Bool, x u = true ∧ C.eval (List.ofFn x) = false := by
    intro u
    refine ⟨pairInput u u, by simp [pairInput], ?_⟩
    change circuitFun n C (pairInput u u) = false
    rw [hL.2.1]
    exact graphFun_single_false G u
  have hBel_iff : ∀ j, Bel n C j ↔ BelowF G C j := by
    intro j
    simp only [Bel, BelowF, W_eq_gateVal]
    constructor
    · intro h x hx
      have := h x hx
      change circuitFun n C x = true at this
      rwa [hL.2.1] at this
    · intro h x hx
      change circuitFun n C x = true
      rw [hL.2.1]
      exact h x hx
  have hmain := M1528.P1.S98.main_abs n C hLeast hT_ex hV (InCone n C)
    (fun i k hk hm => M1528.P1.S98.inCone_c1 n C hA i k hk hm)
    (fun t i k hk hc hm => M1528.P1.S98.inCone_c2 n C hA t i k hk hc hm)
    (fun t s ht hs hopt hBt hops => hT t ht s hs hopt ((hBel_iff t).mp hBt) hops)
  refine ⟨hmain.2.1, ?_⟩
  intro j
  suffices hd : ∀ d j, j < C.gates.length → C.gates.length - j = d → BelowF G C j →
      OrR n C C.output (n + j) by
    intro hj hB
    exact hd (C.gates.length - j) j hj rfl hB
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro j hj hd hB
    by_cases hjo : n + j = C.output
    · rw [hjo]; exact Relation.ReflTransGen.refl
    · obtain ⟨r, hr_lt, hmem, _, hrop, hrBel⟩ := hmain.1 j hj ((hBel_iff j).mpr hB) hjo
      have hjr : j < r := by
        obtain ⟨_, a, b, hab, ha, hb⟩ := hA r hr_lt
        rw [hab] at hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        omega
      have hreach_r := ih (C.gates.length - r) (by omega) r hr_lt rfl ((hBel_iff r).mp hrBel)
      exact hreach_r.tail ⟨r, rfl, hr_lt, hrop, hmem⟩
lemma ustar_edge_structure {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h4 : NoFourCycle G) (hE : G.edgeFinset.Nonempty)
    (hL : IsLeastAO G C) (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g})
    (u v : Fin n) (huv : G.Adj u v) (hU : s(u, v) ∈ Ustar G C) :
    gateVal n C g (pairInput u v) = true ∧
    (u ∈ wmax G C g ∨ v ∈ wmax G C g) ∧
    ((∃ a ∈ centreless G C, ∃ b : Fin 2, opnd C a b = n + g ∧
      side (n := n) C a (1 - b) ⊆ wmax G C g ∧
      (u ∈ side (n := n) C a (1 - b) ∨ v ∈ side (n := n) C a (1 - b))) ∨
    (∃ a ∈ tops G C, a ∉ centreless G C ∧ ∃ b : Fin 2,
      OrReaches n C (opnd C a b) g ∧
      (∃ m ∈ mixing G C, OrReaches n C (opnd C a b) m ∧
        n + g ∈ (gateAt C m).inputs ∧
        ∃ y ∈ (gateAt C m).inputs, y ≠ n + g ∧
          ∃ um ∈ orIn n C y, gateVal n C g (pairInput um um) = false ∧
            um ∈ side (n := n) C a b ∧
            (∃ z ∈ wmax G C g, G.Adj um z ∧ (z = u ∨ z = v) ∧ z ∈ side (n := n) C a (1 - b) ∧
              (side (n := n) C a b = {um} → um ∈ formU G C g) ∧
              (side (n := n) C a b ≠ {um} → z ∈ formZ G C g))))) := by
  have hA : AO n C := AO_of_IsAO2 n C hL.1
  obtain ⟨⟨_, hout_eq⟩, _⟩ := bel_reaches_output G C hE hL hT
  have hCeval : W n C (pairInput u v) C.output = true := by
    change circuitFun n C (pairInput u v) = true
    rw [hL.2.1, graphFun_pair]
    exact huv
  obtain ⟨v0, hrv0, hleaf0, hWv0⟩ := orR_leaf_true n C hA (pairInput u v) C.output (by omega) hCeval
  have hBel_out : ∀ x : Fin n → Bool, W n C x C.output = true → graphFun G ∅ x = true := by
    intro x hx
    change circuitFun n C x = true at hx
    rwa [hL.2.1] at hx
  rcases hleaf0 with hv0n | ⟨a, rfl, ha_lt, ha_op⟩
  · exfalso
    have hW1 : W n C (pairInput ⟨v0, hv0n⟩ ⟨v0, hv0n⟩) C.output = true :=
      orR_mono n C hA _ _ _ hrv0 (by rw [M1528.P2.W_input n C _ v0 hv0n]; simp [pairInput])
    have hF := hBel_out _ hW1
    rw [graphFun_single_false G ⟨v0, hv0n⟩] at hF
    exact Bool.noConfusion hF
  have ha_bel : BelowF G C a := fun x hx => hBel_out x (orR_mono n C hA x C.output (n + a) hrv0 hx)
  have ha_top : a ∈ tops G C := by
    simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range]
    exact ⟨ha_lt, ha_op, ha_bel⟩
  have hnotStar : s(u, v) ∉ starEdges G C := (Finset.mem_sdiff.mp hU).2
  have hnotCross : s(u, v) ∉ (side (n := n) C a 0 ×ˢ side (n := n) C a 1).image (fun p => s(p.1, p.2)) := by
    intro hmem
    apply hnotStar
    simp only [starEdges, Finset.mem_biUnion]
    exact ⟨a, ha_top, hmem⟩
  by_cases haCL : a ∈ centreless G C
  · obtain ⟨b, hgb, _, hsubW, hga⟩ := thm_1503 n G C hE hL hT g hg a haCL
    obtain ⟨hgtrue, huv_side⟩ := hga u v hWv0
    have huvW : u ∈ wmax G C g ∨ v ∈ wmax G C g := by
      rcases huv_side with hu | hv
      · exact Or.inl (hsubW hu)
      · exact Or.inr (hsubW hv)
    exact ⟨hgtrue, huvW, Or.inl ⟨a, haCL, b, hgb, hsubW, huv_side⟩⟩
  ·
    have hside_ne : ∀ t : Fin 2, (side (n := n) C a t).Nonempty := by
      intro t
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      apply haCL
      simp only [centreless, Finset.mem_filter]
      refine ⟨ha_top, ?_⟩
      fin_cases t
      · exact Or.inl hne
      · exact Or.inr hne
    rw [M1528.P2.W_and n C _ a ha_lt ha_op (opnd C a 0) (opnd C a 1) (opnd_eq n C hA a ha_lt)
      (opnd_lt' hA a ha_lt 0) (opnd_lt' hA a ha_lt 1),
      Bool.and_eq_true] at hWv0
    obtain ⟨_, _, _, _, _, htop_cone⟩ := junk_single_props G C hL hT g hg
    have hex_b : ∃ b : Fin 2, OrReaches n C (opnd C a b) g := by
      by_contra hno
      push Not at hno
      have hleaf_in : ∀ t : Fin 2, ∃ w ∈ side (n := n) C a t, pairInput u v w = true := by
        intro t
        have hWt : W n C (pairInput u v) (opnd C a t) = true := by
          fin_cases t <;> [exact hWv0.1; exact hWv0.2]
        obtain ⟨w, hrw, hlw, hWw⟩ := orR_leaf_true n C hA (pairInput u v) (opnd C a t)
          (by have := opnd_lt' hA a ha_lt t; omega) hWt
        rcases hlw with hwn | ⟨h, rfl, hh_lt, hh_op⟩
        · rw [M1528.P2.W_input n C _ w hwn] at hWw
          exact ⟨⟨w, hwn⟩, (mem_orIn n C hA (opnd C a t)
            (by have := opnd_lt' hA a ha_lt t; omega) ⟨w, hwn⟩).mpr hrw, hWw⟩
        · exfalso
          have hmem : opnd C a t ∈ (gateAt C a).inputs := by
            have := opnd_eq n C hA a ha_lt
            fin_cases t <;> rw [this] <;> simp
          have hic : InCone n C h a := by
            by_cases hlt : opnd C a t < n
            · have := orR_le n C hA _ _ hrw; omega
            · obtain ⟨k, hkeq⟩ : ∃ k, opnd C a t = n + k := ⟨opnd C a t - n, by omega⟩
              rcases orR_cone n C hA h (opnd C a t) hrw k hkeq
                (by have := opnd_lt' hA a ha_lt t; omega) with rfl | hc
              · exact M1528.P2.inCone_c1 n C hA h a ha_lt (hkeq ▸ hmem)
              · exact M1528.P2.inCone_c2 n C hA h k a ha_lt hc (hkeq ▸ hmem)
          have hhg := htop_cone a ha_top h hh_lt hh_op hic
          rw [hhg] at hrw
          have hg_lt := (junk_single_props G C hL hT g hg).1
          exact hno t (orR_orReaches n C hA g hg_lt (opnd C a t)
            (by have := opnd_lt' hA a ha_lt t; omega) hrw)
      obtain ⟨w0, hw0, hp0⟩ := hleaf_in 0
      obtain ⟨w1, hw1, hp1⟩ := hleaf_in 1
      rw [pairInput_true] at hp0 hp1
      have hne_w : w0 ≠ w1 := by
        intro heq; subst heq
        have hadj := M1528.P2.sem_adj n C hA a ha_lt ha_op (opnd C a) (opnd_eq n C hA a ha_lt) w0 w0
          ((mem_orIn n C hA _ (by have := opnd_lt' hA a ha_lt 0; omega) w0).mp hw0)
          ((mem_orIn n C hA _ (by have := opnd_lt' hA a ha_lt 1; omega) w0).mp hw1)
        have hF := ha_bel (pairInput w0 w0) hadj
        rw [graphFun_single_false G w0] at hF
        exact Bool.noConfusion hF
      apply hnotCross
      simp only [Finset.mem_image, Finset.mem_product]
      rcases hp0 with h0 | h0 <;> rcases hp1 with h1 | h1
      · exact absurd (h0.trans h1.symm) hne_w
      · exact ⟨(w0, w1), ⟨hw0, hw1⟩, by rw [h0, h1]⟩
      · exact ⟨(w0, w1), ⟨hw0, hw1⟩, by rw [h0, h1, Sym2.eq_swap]⟩
      · exact absurd (h0.trans h1.symm) hne_w
    obtain ⟨b, hb_reach⟩ := hex_b
    obtain ⟨m, hm_mix, hm_reach, hgm⟩ := thm_1505 n G C h4 hE hL hT g hg a ha_top b hb_reach (hside_ne b)
    have hm_lt : m < C.gates.length := by
      simp only [mixing, orN, gatesWhere, Finset.mem_filter, Finset.mem_range] at hm_mix
      exact hm_mix.1.1
    obtain ⟨_, y0, y1, hmin, _, _⟩ := hA m hm_lt
    have hex_y : ∃ y ∈ (gateAt C m).inputs, y ≠ n + g := by
      have hm_xor : (orIn n C (opnd C m 0) = ∅) ≠ (orIn n C (opnd C m 1) = ∅) := by
        simp only [mixing, Finset.mem_filter] at hm_mix
        exact hm_mix.2
      have h0eq : opnd C m 0 = y0 := by simp [opnd, hmin]
      have h1eq : opnd C m 1 = y1 := by simp [opnd, hmin]
      rw [h0eq, h1eq] at hm_xor
      rw [hmin] at hgm ⊢
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hgm ⊢
      rcases hgm with rfl | rfl
      · refine ⟨y1, Or.inr rfl, fun heq => hm_xor (by rw [heq])⟩
      · refine ⟨y0, Or.inl rfl, fun heq => hm_xor (by rw [heq])⟩
    obtain ⟨y, hy_in, hy_ne⟩ := hex_y
    obtain ⟨⟨um, hum_y, hum_g⟩, hrest⟩ := thm_1506 n G C h4 hE hL hT g hg m hm_mix hgm y hy_in hy_ne
    obtain ⟨hum_side, hpair_res, hsubW_if⟩ := hrest um hum_y a ha_top b hm_reach
    have ha_val : gateVal n C a (pairInput u v) = true := by
      rw [← W_eq_gateVal, W_and n C _ a ha_lt ha_op (opnd C a 0) (opnd C a 1)
        (opnd_eq n C hA a ha_lt) (opnd_lt' hA a ha_lt 0)
        (opnd_lt' hA a ha_lt 1), Bool.and_eq_true]
      exact hWv0
    obtain ⟨hg_true, z, hzW, humz, hzev⟩ := hpair_res u v huv ha_val hnotCross
    have huvW : u ∈ wmax G C g ∨ v ∈ wmax G C g := by
      rcases hzev with rfl | rfl
      · exact Or.inl hzW
      · exact Or.inr hzW
    have hnot_other : ¬ OrR n C (opnd C a (1 - b)) (n + g) := by
      intro hoth
      have hbg_orR := orReaches_orR n C (opnd C a b) (by have := opnd_lt' hA a ha_lt b; omega) g hb_reach
      have hboth : ∀ x, W n C x (n + g) = true → W n C x (n + a) = true := by
        intro x hgx
        have h0 : W n C x (opnd C a b) = true := orR_mono n C hA x _ _ hbg_orR hgx
        have h1 : W n C x (opnd C a (1 - b)) = true := orR_mono n C hA x _ _ hoth hgx
        rw [W_and n C x a ha_lt ha_op (opnd C a 0) (opnd C a 1) (opnd_eq n C hA a ha_lt)
          (opnd_lt' hA a ha_lt 0) (opnd_lt' hA a ha_lt 1), Bool.and_eq_true]
        fin_cases b
        · exact ⟨h0, h1⟩
        · exact ⟨h1, h0⟩
      exact (junk_single_props G C hL hT g hg).2.2.1 (fun x hx => ha_bel x (hboth x hx))
    have hnoAnd_other : ∀ h < C.gates.length, (gateAt C h).op = GateOp.and →
        ¬ OrR n C (opnd C a (1 - b)) (n + h) := by
      intro h hh hop hr
      have hmem : opnd C a (1 - b) ∈ (gateAt C a).inputs := by
        have := opnd_eq n C hA a ha_lt
        fin_cases b <;> rw [this] <;> simp
      have hic : InCone n C h a := by
        by_cases hlt : opnd C a (1 - b) < n
        · have := orR_le n C hA _ _ hr; omega
        · obtain ⟨k, hkeq⟩ : ∃ k, opnd C a (1 - b) = n + k := ⟨opnd C a (1 - b) - n, by omega⟩
          rcases orR_cone n C hA h (opnd C a (1 - b)) hr k hkeq
            (by have := opnd_lt' hA a ha_lt (1 - b); omega) with rfl | hc
          · exact M1528.P2.inCone_c1 n C hA h a ha_lt (hkeq ▸ hmem)
          · exact M1528.P2.inCone_c2 n C hA h k a ha_lt hc (hkeq ▸ hmem)
      have hhg := htop_cone a ha_top h hh hop hic
      rw [hhg] at hr
      exact hnot_other hr
    have hW_other : W n C (pairInput u v) (opnd C a (1 - b)) = true := by
      fin_cases b
      · exact hWv0.2
      · exact hWv0.1
    obtain ⟨w_oth, hw_oth_side, hw_oth_uv⟩ :=
      (pure_or_wire_eval C hA (opnd C a (1 - b))
        (by have := opnd_lt' hA a ha_lt (1 - b); omega) hnoAnd_other).2
        (pairInput u v) |>.mp hW_other
    have hbiclique : ∀ x ∈ side (n := n) C a b, ∀ y ∈ side (n := n) C a (1 - b), G.Adj x y := by
      intro x hx y hy
      have hWx : W n C (pairInput x y) (opnd C a b) = true := orR_mono n C hA (pairInput x y) (opnd C a b) x.val
        ((mem_orIn n C hA _ (by have := opnd_lt' hA a ha_lt b; omega) x).mp hx)
        (by rw [M1528.P2.W_input n C _ x.val x.isLt]; simp [pairInput])
      have hWy : W n C (pairInput x y) (opnd C a (1 - b)) = true := orR_mono n C hA (pairInput x y) (opnd C a (1 - b)) y.val
        ((mem_orIn n C hA _ (by have := opnd_lt' hA a ha_lt (1 - b); omega) y).mp hy)
        (by rw [M1528.P2.W_input n C _ y.val y.isLt]; simp [pairInput])
      have hWa : W n C (pairInput x y) (n + a) = true := by
        rw [W_and n C _ a ha_lt ha_op (opnd C a 0) (opnd C a 1) (opnd_eq n C hA a ha_lt)
          (opnd_lt' hA a ha_lt 0) (opnd_lt' hA a ha_lt 1), Bool.and_eq_true]
        fin_cases b
        · exact ⟨hWx, hWy⟩
        · exact ⟨hWy, hWx⟩
      have hF := ha_bel (pairInput x y) hWa
      rwa [graphFun_pair] at hF
    have hoth_sub_W : side (n := n) C a (1 - b) ⊆ wmax G C g := by
      intro w hw
      simp only [wmax, Finset.mem_filter, Finset.mem_univ, true_and]
      intro x hgx hxw
      have h0 : W n C x (opnd C a b) = true :=
        orR_mono n C hA x _ _ (orReaches_orR n C _ (by have := opnd_lt' hA a ha_lt b; omega) _ hb_reach) hgx
      have h1 : W n C x (opnd C a (1 - b)) = true :=
        orR_mono n C hA x _ _
          ((mem_orIn n C hA _ (by have := opnd_lt' hA a ha_lt (1 - b); omega) w).mp hw)
          (by rw [M1528.P2.W_input n C x w.val w.isLt]; exact hxw)
      have hWa : W n C x (n + a) = true := by
        rw [W_and n C x a ha_lt ha_op (opnd C a 0) (opnd C a 1) (opnd_eq n C hA a ha_lt)
          (opnd_lt' hA a ha_lt 0) (opnd_lt' hA a ha_lt 1), Bool.and_eq_true]
        fin_cases b
        · exact ⟨h0, h1⟩
        · exact ⟨h1, h0⟩
      exact ha_bel x hWa
    rw [pairInput_true] at hw_oth_uv
    refine ⟨hg_true, huvW, Or.inr ⟨a, ha_top, haCL, b, hb_reach, m, hm_mix, hm_reach, hgm,
      y, hy_in, hy_ne, um, hum_y, hum_g, hum_side, w_oth, hoth_sub_W hw_oth_side,
      hbiclique um hum_side w_oth hw_oth_side, hw_oth_uv, hw_oth_side, ?_, ?_⟩⟩
    · intro hsing
      simp only [formU, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨a, ha_top, b, hsing, hb_reach⟩
    · intro hne_sing
      have hcard2 : 2 ≤ (side (n := n) C a b).card := by
        by_contra hlt2
        have hle1 : (side (n := n) C a b).card ≤ 1 := by omega
        obtain ⟨x, hx⟩ := Finset.card_eq_one.mp (le_antisymm hle1 (Finset.card_pos.mpr ⟨um, hum_side⟩))
        have : um = x := by rw [hx, Finset.mem_singleton] at hum_side; exact hum_side
        exact hne_sing (by rw [hx, this])
      have hoth_le1 : (side (n := n) C a (1 - b)).card ≤ 1 := by
        rcases M1528.P2.biclique_star G (nfc n G h4) (side (n := n) C a b)
          (side (n := n) C a (1 - b)) hbiclique with h1 | h2
        · omega
        · exact h2
      have hoth_eq : side (n := n) C a (1 - b) = {w_oth} := by
        have hw_side' : w_oth ∈ side (n := n) C a (1 - b) := hw_oth_side
        obtain ⟨x, hx⟩ := Finset.card_eq_one.mp (le_antisymm hoth_le1
          (Finset.card_pos.mpr ⟨w_oth, hw_side'⟩))
        have : w_oth = x := by rw [hx, Finset.mem_singleton] at hw_side'; exact hw_side'
        rw [hx, this]
      simp only [formZ, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨a, ha_top, b, hcard2, hb_reach, hoth_eq⟩
lemma erase_W_le_of_le {n : ℕ} (C : Circuit) (hA : AO n C) (j w : ℕ)
    (hj : j < C.gates.length) (hw : w < n + j) (x : Fin n → Bool)
    (hle : W n C x w = true → W n C x (n + j) = true) :
    ∀ u, u < n + C.gates.length →
      W n (eraseC n C j w) x (aliasWire (n + j) w u) = true → W n C x u = true := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu hD
    by_cases h1 : u < n + j
    · have hal : aliasWire (n + j) w u = u := by
        unfold aliasWire M1528.P1.S98.shiftDown; split_ifs <;> omega
      rw [hal, erase_W_lt n C j w hj x u h1] at hD
      exact hD
    · by_cases h2 : u = n + j
      · subst h2
        have hal : aliasWire (n + j) w (n + j) = w := by simp [aliasWire]
        rw [hal, erase_W_lt n C j w hj x w hw] at hD
        exact hle hD
      · obtain ⟨k, rfl⟩ : ∃ k, u = n + (k + 1) := ⟨u - n - 1, by omega⟩
        have hk : k + 1 < C.gates.length := by omega
        have hkj : j ≤ k := by omega
        have hal : aliasWire (n + j) w (n + (k + 1)) = n + k := by
          unfold aliasWire M1528.P1.S98.shiftDown; split_ifs <;> omega
        rw [hal] at hD
        have hlenD : k < (eraseC n C j w).gates.length := by
          have := erase_length n C j w hj; omega
        obtain ⟨hop, a, b, hab, ha, hb⟩ := hA (k + 1) hk
        have hgD := erase_gateAt_ge n C j w k hj hkj hk
        have haD : aliasWire (n + j) w a < n + k :=
          M1528.P1.S98.alias_lt (n + j) w a (n + k) (by omega) hw (by omega)
        have hbD : aliasWire (n + j) w b < n + k :=
          M1528.P1.S98.alias_lt (n + j) w b (n + k) (by omega) hw (by omega)
        have hinD : (gateAt (eraseC n C j w) k).inputs = [aliasWire (n + j) w a, aliasWire (n + j) w b] := by
          rw [hgD]; simp [aliasGate, hab]
        rcases hop with hop | hop
        · have hopD : (gateAt (eraseC n C j w) k).op = GateOp.and := by rw [hgD]; exact hop
          rw [W_and n (eraseC n C j w) x k hlenD hopD _ _ hinD haD hbD, Bool.and_eq_true] at hD
          rw [W_and n C x (k + 1) hk hop a b hab ha hb, Bool.and_eq_true]
          exact ⟨ih a ha (by omega) hD.1, ih b hb (by omega) hD.2⟩
        · have hopD : (gateAt (eraseC n C j w) k).op = GateOp.or := by rw [hgD]; exact hop
          rw [W_or n (eraseC n C j w) x k hlenD hopD _ _ hinD haD hbD, Bool.or_eq_true] at hD
          rw [W_or n C x (k + 1) hk hop a b hab ha hb, Bool.or_eq_true]
          rcases hD with h | h
          · exact Or.inl (ih a ha (by omega) h)
          · exact Or.inr (ih b hb (by omega) h)
lemma erase_W_ge_of_ge {n : ℕ} (C : Circuit) (hA : AO n C) (j w : ℕ)
    (hj : j < C.gates.length) (hw : w < n + j) (x : Fin n → Bool)
    (hge : W n C x (n + j) = true → W n C x w = true) :
    ∀ u, u < n + C.gates.length →
      W n C x u = true → W n (eraseC n C j w) x (aliasWire (n + j) w u) = true := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu hC
    by_cases h1 : u < n + j
    · have hal : aliasWire (n + j) w u = u := by
        unfold aliasWire M1528.P1.S98.shiftDown; split_ifs <;> omega
      rw [hal, erase_W_lt n C j w hj x u h1]
      exact hC
    · by_cases h2 : u = n + j
      · subst h2
        have hal : aliasWire (n + j) w (n + j) = w := by simp [aliasWire]
        rw [hal, erase_W_lt n C j w hj x w hw]
        exact hge hC
      · obtain ⟨k, rfl⟩ : ∃ k, u = n + (k + 1) := ⟨u - n - 1, by omega⟩
        have hk : k + 1 < C.gates.length := by omega
        have hkj : j ≤ k := by omega
        have hal : aliasWire (n + j) w (n + (k + 1)) = n + k := by
          unfold aliasWire M1528.P1.S98.shiftDown; split_ifs <;> omega
        rw [hal]
        have hlenD : k < (eraseC n C j w).gates.length := by
          have := erase_length n C j w hj; omega
        obtain ⟨hop, a, b, hab, ha, hb⟩ := hA (k + 1) hk
        have hgD := erase_gateAt_ge n C j w k hj hkj hk
        have haD : aliasWire (n + j) w a < n + k :=
          M1528.P1.S98.alias_lt (n + j) w a (n + k) (by omega) hw (by omega)
        have hbD : aliasWire (n + j) w b < n + k :=
          M1528.P1.S98.alias_lt (n + j) w b (n + k) (by omega) hw (by omega)
        have hinD : (gateAt (eraseC n C j w) k).inputs = [aliasWire (n + j) w a, aliasWire (n + j) w b] := by
          rw [hgD]; simp [aliasGate, hab]
        rcases hop with hop | hop
        · have hopD : (gateAt (eraseC n C j w) k).op = GateOp.and := by rw [hgD]; exact hop
          rw [W_and n C x (k + 1) hk hop a b hab ha hb, Bool.and_eq_true] at hC
          rw [W_and n (eraseC n C j w) x k hlenD hopD _ _ hinD haD hbD, Bool.and_eq_true]
          exact ⟨ih a ha (by omega) hC.1, ih b hb (by omega) hC.2⟩
        · have hopD : (gateAt (eraseC n C j w) k).op = GateOp.or := by rw [hgD]; exact hop
          rw [W_or n C x (k + 1) hk hop a b hab ha hb, Bool.or_eq_true] at hC
          rw [W_or n (eraseC n C j w) x k hlenD hopD _ _ hinD haD hbD, Bool.or_eq_true]
          rcases hC with h | h
          · exact Or.inl (ih a ha (by omega) h)
          · exact Or.inr (ih b hb (by omega) h)
lemma erase_orR_mono {n : ℕ} (C : Circuit) (hA : AO n C) (j w : ℕ)
    (hj : j < C.gates.length) (hj_and : (gateAt C j).op = GateOp.and)
    (hw : w < n + j) (x : Fin n → Bool) {u v : ℕ} (hr : OrR n C u v)
    (hv : W n (eraseC n C j w) x (aliasWire (n + j) w v) = true) :
    W n (eraseC n C j w) x (aliasWire (n + j) w u) = true := by
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head hstep _ ih =>
    obtain ⟨k, rfl, hk, hkop, hkin⟩ := hstep
    have hkj_ne : k ≠ j := by intro heq; subst heq; rw [hj_and] at hkop; exact GateOp.noConfusion hkop
    obtain ⟨_, a, b, hab, ha, hb⟩ := hA k hk
    have hD_ao : AO n (eraseC n C j w) := erase_AO n C j w hA hj hw
    have hlenD : (eraseC n C j w).gates.length + 1 = C.gates.length := erase_length n C j w hj
    by_cases hkj : k < j
    · have hal : aliasWire (n + j) w (n + k) = n + k := by
        unfold aliasWire M1528.P1.S98.shiftDown; split_ifs <;> omega
      rw [hal]
      have hgD : gateAt (eraseC n C j w) k = gateAt C k := erase_gateAt_lt n C j w k hj hkj
      rw [W_or n (eraseC n C j w) x k (by omega) (by rw [hgD]; exact hkop) a b (by rw [hgD]; exact hab) ha hb,
        Bool.or_eq_true]
      rw [hab] at hkin
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hkin
      rcases hkin with h1 | h2
      · rw [h1] at ih
        have hal_a : aliasWire (n + j) w a = a := by
          unfold aliasWire M1528.P1.S98.shiftDown; split_ifs <;> omega
        rw [hal_a] at ih; exact Or.inl ih
      · rw [h2] at ih
        have hal_b : aliasWire (n + j) w b = b := by
          unfold aliasWire M1528.P1.S98.shiftDown; split_ifs <;> omega
        rw [hal_b] at ih; exact Or.inr ih
    · have hk1 : j < k := by omega
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have hal : aliasWire (n + j) w (n + (k' + 1)) = n + k' := by
        unfold aliasWire M1528.P1.S98.shiftDown; split_ifs <;> omega
      rw [hal]
      have hgD := erase_gateAt_ge n C j w k' hj (by omega) hk
      have haD := M1528.P1.S98.alias_lt (n + j) w a (n + k') (by omega) hw (by omega)
      have hbD := M1528.P1.S98.alias_lt (n + j) w b (n + k') (by omega) hw (by omega)
      have hinD : (gateAt (eraseC n C j w) k').inputs = [aliasWire (n + j) w a, aliasWire (n + j) w b] := by
        rw [hgD]; simp [aliasGate, hab]
      rw [W_or n (eraseC n C j w) x k' (by omega) (by rw [hgD]; exact hkop) _ _ hinD haD hbD,
        Bool.or_eq_true]
      rw [hab] at hkin
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hkin
      rcases hkin with rfl | rfl
      · exact Or.inl ih
      · exact Or.inr ih
lemma erase_pure_or_eq {n : ℕ} (C : Circuit) (hA : AO n C) (j w : ℕ)
    (hj : j < C.gates.length) (hj_and : (gateAt C j).op = GateOp.and)
    (hw : w < n + j) (x : Fin n → Bool) :
    ∀ r, r < n + C.gates.length →
      (∀ h < C.gates.length, (gateAt C h).op = GateOp.and → ¬ OrR n C r (n + h)) →
      W n (eraseC n C j w) x (aliasWire (n + j) w r) = W n C x r := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro hr hnoAnd
    by_cases hrn : r < n
    · have hal : aliasWire (n + j) w r = r := by
        unfold aliasWire M1528.P1.S98.shiftDown; split_ifs <;> omega
      rw [hal, erase_W_lt n C j w hj x r (by omega)]
    · obtain ⟨k, rfl⟩ : ∃ k, r = n + k := ⟨r - n, by omega⟩
      have hk : k < C.gates.length := by omega
      obtain ⟨hop, a, b, hab, ha, hb⟩ := hA k hk
      rcases hop with hop | hop
      · exact absurd Relation.ReflTransGen.refl (hnoAnd k hk hop)
      · have hkj_ne : k ≠ j := by intro heq; subst heq; rw [hj_and] at hop; exact GateOp.noConfusion hop
        have hstep_a : OrStep n C (n + k) a := ⟨k, rfl, hk, hop, by rw [hab]; simp⟩
        have hstep_b : OrStep n C (n + k) b := ⟨k, rfl, hk, hop, by rw [hab]; simp⟩
        have iha := ih a ha (by omega) (fun h hh hhop hr' => hnoAnd h hh hhop (Relation.ReflTransGen.head hstep_a hr'))
        have ihb := ih b hb (by omega) (fun h hh hhop hr' => hnoAnd h hh hhop (Relation.ReflTransGen.head hstep_b hr'))
        have hlenD : (eraseC n C j w).gates.length + 1 = C.gates.length := erase_length n C j w hj
        rw [W_or n C x k hk hop a b hab ha hb]
        by_cases hkj : k < j
        · have hal : aliasWire (n + j) w (n + k) = n + k := by
            unfold aliasWire M1528.P1.S98.shiftDown; split_ifs <;> omega
          have hala : aliasWire (n + j) w a = a := by
            unfold aliasWire M1528.P1.S98.shiftDown; split_ifs <;> omega
          have halb : aliasWire (n + j) w b = b := by
            unfold aliasWire M1528.P1.S98.shiftDown; split_ifs <;> omega
          rw [hal]
          have hgD := erase_gateAt_lt n C j w k hj hkj
          rw [W_or n (eraseC n C j w) x k (by omega) (by rw [hgD]; exact hop) a b (by rw [hgD]; exact hab) ha hb]
          rw [hala] at iha; rw [halb] at ihb
          rw [iha, ihb]
        · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
          have hal : aliasWire (n + j) w (n + (k' + 1)) = n + k' := by
            unfold aliasWire M1528.P1.S98.shiftDown; split_ifs <;> omega
          rw [hal]
          have hgD := erase_gateAt_ge n C j w k' hj (by omega) hk
          have haD := M1528.P1.S98.alias_lt (n + j) w a (n + k') (by omega) hw (by omega)
          have hbD := M1528.P1.S98.alias_lt (n + j) w b (n + k') (by omega) hw (by omega)
          have hinD : (gateAt (eraseC n C j w) k').inputs = [aliasWire (n + j) w a, aliasWire (n + j) w b] := by
            rw [hgD]; simp [aliasGate, hab]
          rw [W_or n (eraseC n C j w) x k' (by omega) (by rw [hgD]; exact hop) _ _ hinD haD hbD, iha, ihb]
theorem replace_gate_by_wire {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hE : G.edgeFinset.Nonempty) (hL : IsLeastAO G C) (hT : TopForm G C)
    (g : ℕ) (hg : junk G C = {g}) (w : ℕ) (hw : w < n + g)
    (hU : ∀ u v : Fin n, G.Adj u v → s(u, v) ∈ Ustar G C → W n C (pairInput u v) w = true)
    (hsound : (∀ x : Fin n → Bool, W n C x w = true → W n C x (n + g) = true) ∨
      (∃ w0 : Fin n, wmax G C g = {w0} ∧
        ∀ x : Fin n → Bool, x w0 = true → W n C x w = true → graphFun G ∅ x = true)) :
    False := by
  have hA : AO n C := AO_of_IsAO2 n C hL.1
  obtain ⟨hg_lt, hg_op, hg_notB, _, _, htop_cone⟩ := junk_single_props G C hL hT g hg
  obtain ⟨⟨hout_ge, hout_eq⟩, hbel_reach⟩ := bel_reaches_output G C hE hL hT
  let D := eraseC n C g w
  have hD_AO : AO n D := erase_AO n C g w hA hg_lt hw
  have hD_len : D.gates.length + 1 = C.gates.length := erase_length n C g w hg_lt
  have hD_fun : circuitFun n D = graphFun G ∅ := by
    funext x
    rw [Bool.eq_iff_iff]
    change W n D x (aliasWire (n + g) w C.output) = true ↔ graphFun G ∅ x = true
    constructor
    ·
      intro hDx
      rcases hsound with hle | ⟨w0, hW0, hw0_sound⟩
      · have hCx := erase_W_le_of_le C hA g w hg_lt hw x (hle x) C.output (by omega) hDx
        change circuitFun n C x = true at hCx
        rwa [hL.2.1] at hCx
      · by_contra hFx
        have hFx_false : graphFun G ∅ x = false := Bool.eq_false_iff.mpr hFx
        by_cases hcond : W n C x w = true → W n C x (n + g) = true
        · have hCx := erase_W_le_of_le C hA g w hg_lt hw x hcond C.output (by omega) hDx
          change circuitFun n C x = true at hCx
          rw [hL.2.1] at hCx
          exact hFx hCx
        · push Not at hcond
          obtain ⟨hWw, _⟩ := hcond
          have hxw0 : x w0 = false := by
            by_contra ht
            have h1 : x w0 = true := by cases h : x w0 <;> simp_all
            exact hFx (hw0_sound x h1 hWw)
          have hbel_false : ∀ k, k < C.gates.length → BelowF G C k →
              W n D x (aliasWire (n + g) w (n + k)) = false := by
            intro k
            induction k using Nat.strong_induction_on with
            | _ k ihk =>
              intro hk hBk
              rw [Bool.eq_false_iff]
              intro hDk
              obtain ⟨hop, a, b, hab, ha, hb⟩ := hA k hk
              have hkg_ne : k ≠ g := by
                intro heq; subst heq; exact hg_notB hBk
              have hlenD : D.gates.length + 1 = C.gates.length := hD_len
              have hstep_D : ∀ op : GateOp, (gateAt C k).op = op →
                  W n D x (aliasWire (n + g) w (n + k)) =
                  op.eval [W n D x (aliasWire (n + g) w a), W n D x (aliasWire (n + g) w b)] := by
                intro op hop_eq
                by_cases hkj : k < g
                · have hal : aliasWire (n + g) w (n + k) = n + k := by
                    unfold aliasWire M1528.P1.S98.shiftDown; split_ifs <;> omega
                  have hala : aliasWire (n + g) w a = a := by
                    unfold aliasWire M1528.P1.S98.shiftDown; split_ifs <;> omega
                  have halb : aliasWire (n + g) w b = b := by
                    unfold aliasWire M1528.P1.S98.shiftDown; split_ifs <;> omega
                  have hgD := erase_gateAt_lt n C g w k hg_lt hkj
                  rw [hal, hala, halb, W_gate n D x k (by omega), hgD, hop_eq, hab]
                  simp [ha, hb]
                · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
                  have hal : aliasWire (n + g) w (n + (k' + 1)) = n + k' := by
                    unfold aliasWire M1528.P1.S98.shiftDown; split_ifs <;> omega
                  have hgD := erase_gateAt_ge n C g w k' hg_lt (by omega) hk
                  have haD := M1528.P1.S98.alias_lt (n + g) w a (n + k') (by omega) hw (by omega)
                  have hbD := M1528.P1.S98.alias_lt (n + g) w b (n + k') (by omega) hw (by omega)
                  rw [hal, W_gate n D x k' (by omega), hgD]
                  simp [aliasGate, hop_eq, hab, haD, hbD]
              rcases hop with hop | hop
              ·
                have hk_top : k ∈ tops G C := by
                  simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range]
                  exact ⟨hk, hop, hBk⟩
                rw [hstep_D GateOp.and hop] at hDk
                simp only [GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true,
                  Bool.and_eq_true] at hDk
                have hnoAnd_of_notg : ∀ t : Fin 2, ¬ OrR n C (opnd C k t) (n + g) →
                    ∀ h < C.gates.length, (gateAt C h).op = GateOp.and → ¬ OrR n C (opnd C k t) (n + h) := by
                  intro t hng h hh hhop hr
                  have hmem : opnd C k t ∈ (gateAt C k).inputs := by
                    have := opnd_eq n C hA k hk
                    fin_cases t <;> rw [this] <;> simp
                  have hic : InCone n C h k := by
                    by_cases hlt : opnd C k t < n
                    · have := orR_le n C hA _ _ hr; omega
                    · obtain ⟨r, hreq⟩ : ∃ r, opnd C k t = n + r := ⟨opnd C k t - n, by omega⟩
                      rcases orR_cone n C hA h (opnd C k t) hr r hreq
                        (by have := opnd_lt' hA k hk t; omega) with rfl | hc
                      · exact M1528.P2.inCone_c1 n C hA h k hk (hreq ▸ hmem)
                      · exact M1528.P2.inCone_c2 n C hA h r k hk hc (hreq ▸ hmem)
                  have hhg := htop_cone k hk_top h hh hhop hic
                  subst hhg
                  exact hng hr
                have h0_eq : opnd C k 0 = a := by simp [opnd, hab]
                have h1_eq : opnd C k 1 = b := by simp [opnd, hab]
                by_cases hr0 : OrR n C a (n + g)
                ·
                  have hnr1 : ¬ OrR n C b (n + g) := by
                    intro hr1
                    exact hg_notB (fun y hy => hBk y (by
                      rw [← W_eq_gateVal, W_and n C y k hk hop a b hab ha hb, Bool.and_eq_true]
                      exact ⟨orR_mono n C hA y a (n + g) hr0 hy, orR_mono n C hA y b (n + g) hr1 hy⟩))
                  have hno1 := hnoAnd_of_notg 1 (h1_eq.symm ▸ hnr1)
                  rw [h1_eq] at hno1
                  have hDb_eq := erase_pure_or_eq C hA g w hg_lt hg_op hw x b (by omega) hno1
                  rw [hDb_eq] at hDk
                  obtain ⟨u, hu, hxu⟩ := (pure_or_wire_eval C hA b (by omega) hno1).2 x |>.mp hDk.2
                  have huW : u ∈ wmax G C g := by
                    simp only [wmax, Finset.mem_filter, Finset.mem_univ, true_and]
                    intro y hgy hyu
                    have hy0 := orR_mono n C hA y a (n + g) hr0 hgy
                    have hy1 := orR_mono n C hA y b u.val
                      ((mem_orIn n C hA b (by omega) u).mp hu)
                      (by rw [M1528.P2.W_input n C y u.val u.isLt]; exact hyu)
                    exact hBk y (by
                      rw [← W_eq_gateVal, W_and n C y k hk hop a b hab ha hb, Bool.and_eq_true]
                      exact ⟨hy0, hy1⟩)
                  rw [hW0, Finset.mem_singleton] at huW
                  subst huW
                  rw [hxw0] at hxu
                  exact Bool.noConfusion hxu
                · by_cases hr1 : OrR n C b (n + g)
                  ·
                    have hno0 := hnoAnd_of_notg 0 (h0_eq.symm ▸ hr0)
                    rw [h0_eq] at hno0
                    have hDa_eq := erase_pure_or_eq C hA g w hg_lt hg_op hw x a (by omega) hno0
                    rw [hDa_eq] at hDk
                    obtain ⟨u, hu, hxu⟩ := (pure_or_wire_eval C hA a (by omega) hno0).2 x |>.mp hDk.1
                    have huW : u ∈ wmax G C g := by
                      simp only [wmax, Finset.mem_filter, Finset.mem_univ, true_and]
                      intro y hgy hyu
                      have hy1 := orR_mono n C hA y b (n + g) hr1 hgy
                      have hy0 := orR_mono n C hA y a u.val
                        ((mem_orIn n C hA a (by omega) u).mp hu)
                        (by rw [M1528.P2.W_input n C y u.val u.isLt]; exact hyu)
                      exact hBk y (by
                        rw [← W_eq_gateVal, W_and n C y k hk hop a b hab ha hb, Bool.and_eq_true]
                        exact ⟨hy0, hy1⟩)
                    rw [hW0, Finset.mem_singleton] at huW
                    subst huW
                    rw [hxw0] at hxu
                    exact Bool.noConfusion hxu
                  ·
                    have hno0 := hnoAnd_of_notg 0 (h0_eq.symm ▸ hr0)
                    have hno1 := hnoAnd_of_notg 1 (h1_eq.symm ▸ hr1)
                    rw [h0_eq] at hno0; rw [h1_eq] at hno1
                    rw [erase_pure_or_eq C hA g w hg_lt hg_op hw x a (by omega) hno0,
                      erase_pure_or_eq C hA g w hg_lt hg_op hw x b (by omega) hno1] at hDk
                    have hCk : W n C x (n + k) = true := by
                      rw [W_and n C x k hk hop a b hab ha hb, Bool.and_eq_true]; exact hDk
                    exact hFx (hBk x hCk)
              ·
                rw [hstep_D GateOp.or hop] at hDk
                simp only [GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false,
                  Bool.or_eq_true] at hDk
                have hchild_bel : ∀ c, c ∈ (gateAt C k).inputs → c < n + k →
                    ∃ j, c = n + j ∧ j < k ∧ BelowF G C j := by
                  intro c hc hclt
                  have hstep_c : OrStep n C (n + k) c := ⟨k, rfl, hk, hop, hc⟩
                  by_cases hcn : c < n
                  · exfalso
                    have h1 : W n C (pairInput ⟨c, hcn⟩ ⟨c, hcn⟩) (n + k) = true :=
                      orStep_mono n C hA _ _ _ hstep_c (by rw [M1528.P2.W_input n C _ c hcn]; simp [pairInput])
                    have hF := hBk _ h1
                    rw [graphFun_single_false G ⟨c, hcn⟩] at hF
                    exact Bool.noConfusion hF
                  · refine ⟨c - n, by omega, by omega, fun y hy => hBk y ?_⟩
                    rw [← W_eq_gateVal] at hy
                    exact orStep_mono n C hA y (n + k) c hstep_c (by rwa [show n + (c - n) = c by omega] at hy)
                rcases hDk with hDa | hDb
                · obtain ⟨ja, rfl, hja, hBja⟩ := hchild_bel a (by rw [hab]; simp) ha
                  rw [ihk ja hja (by omega) hBja] at hDa
                  exact Bool.noConfusion hDa
                · obtain ⟨jb, rfl, hjb, hBjb⟩ := hchild_bel b (by rw [hab]; simp) hb
                  rw [ihk jb hjb (by omega) hBjb] at hDb
                  exact Bool.noConfusion hDb
          obtain ⟨k_out, hk_out⟩ : ∃ k_out, C.output = n + k_out := ⟨C.output - n, by omega⟩
          have hk_out_lt : k_out < C.gates.length := by omega
          have hk_out_bel : BelowF G C k_out := by
            intro y hy
            have : W n C y C.output = true := by rwa [hk_out]
            change circuitFun n C y = true at this
            rwa [hL.2.1] at this
          rw [hk_out, hbel_false k_out hk_out_lt hk_out_bel] at hDx
          exact Bool.noConfusion hDx
    ·
      intro hGx
      simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
        Bool.false_or, decide_eq_true_eq] at hGx
      obtain ⟨u, v, huv, hxu, hxv⟩ := hGx
      have hpair_le : ∀ i, pairInput u v i = true → x i = true := by
        intro i hi
        rw [pairInput_true] at hi
        rcases hi with rfl | rfl <;> assumption
      have hD_out_lt : aliasWire (n + g) w C.output < n + D.gates.length := by
        have := M1528.P1.S98.alias_lt (n + g) w C.output (n + D.gates.length) (by omega) hw (by omega)
        exact this
      refine W_mono_input D hD_AO (pairInput u v) x hpair_le _ hD_out_lt ?_
      by_cases hUV : s(u, v) ∈ Ustar G C
      · have hWw := hU u v huv hUV
        have hCpair : W n C (pairInput u v) C.output = true := by
          change circuitFun n C (pairInput u v) = true
          rw [hL.2.1, graphFun_pair]
          exact huv
        exact erase_W_ge_of_ge C hA g w hg_lt hw (pairInput u v) (fun _ => hWw) C.output (by omega) hCpair
      · have hstar : s(u, v) ∈ starEdges G C := by
          have he : s(u, v) ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.mpr huv
          by_contra hns
          exact hUV (Finset.mem_sdiff.mpr ⟨he, hns⟩)
        simp only [starEdges, Finset.mem_biUnion, Finset.mem_image, Finset.mem_product] at hstar
        obtain ⟨a, ha_top, ⟨p, q⟩, ⟨hp, hq⟩, hpq⟩ := hstar
        simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha_top
        have hpair_p : pairInput u v p = true := by
          rw [pairInput_true]
          rcases Sym2.eq_iff.mp hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Or.inl rfl
          · exact Or.inr rfl
        have hpair_q : pairInput u v q = true := by
          rw [pairInput_true]
          rcases Sym2.eq_iff.mp hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Or.inr rfl
          · exact Or.inl rfl
        have hDp : W n D (pairInput u v) (aliasWire (n + g) w (opnd C a 0)) = true := by
          have hr := (mem_orIn n C hA (opnd C a 0)
            (by have := opnd_lt' hA a ha_top.1 0; omega) p).mp hp
          refine erase_orR_mono C hA g w hg_lt hg_op hw (pairInput u v) hr ?_
          have hal : aliasWire (n + g) w p.val = p.val := by
            unfold aliasWire M1528.P1.S98.shiftDown; split_ifs <;> have := p.isLt <;> omega
          rw [hal, W_input n D _ p.val p.isLt]
          exact hpair_p
        have hDq : W n D (pairInput u v) (aliasWire (n + g) w (opnd C a 1)) = true := by
          have hr := (mem_orIn n C hA (opnd C a 1)
            (by have := opnd_lt' hA a ha_top.1 1; omega) q).mp hq
          refine erase_orR_mono C hA g w hg_lt hg_op hw (pairInput u v) hr ?_
          have hal : aliasWire (n + g) w q.val = q.val := by
            unfold aliasWire M1528.P1.S98.shiftDown; split_ifs <;> have := q.isLt <;> omega
          rw [hal, W_input n D _ q.val q.isLt]
          exact hpair_q
        have hDa : W n D (pairInput u v) (aliasWire (n + g) w (n + a)) = true := by
          have hag_ne : a ≠ g := by intro heq; subst heq; exact hg_notB ha_top.2.2
          have hab := opnd_eq n C hA a ha_top.1
          have ha0 := opnd_lt' hA a ha_top.1 0
          have ha1 := opnd_lt' hA a ha_top.1 1
          by_cases hag : a < g
          · have hal : aliasWire (n + g) w (n + a) = n + a := by
              unfold aliasWire M1528.P1.S98.shiftDown; split_ifs <;> omega
            have hal0 : aliasWire (n + g) w (opnd C a 0) = opnd C a 0 := by
              unfold aliasWire M1528.P1.S98.shiftDown; split_ifs <;> omega
            have hal1 : aliasWire (n + g) w (opnd C a 1) = opnd C a 1 := by
              unfold aliasWire M1528.P1.S98.shiftDown; split_ifs <;> omega
            have hgD := erase_gateAt_lt n C g w a hg_lt hag
            rw [hal, W_and n D _ a (by omega) (by rw [hgD]; exact ha_top.2.1)
              (opnd C a 0) (opnd C a 1) (by rw [hgD]; exact hab) ha0 ha1, Bool.and_eq_true]
            rw [hal0] at hDp; rw [hal1] at hDq
            exact ⟨hDp, hDq⟩
          · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
            have hal : aliasWire (n + g) w (n + (a' + 1)) = n + a' := by
              unfold aliasWire M1528.P1.S98.shiftDown; split_ifs <;> omega
            have hgD := erase_gateAt_ge n C g w a' hg_lt (by omega) ha_top.1
            have h0D := M1528.P1.S98.alias_lt (n + g) w (opnd C (a' + 1) 0) (n + a') (by omega) hw (by omega)
            have h1D := M1528.P1.S98.alias_lt (n + g) w (opnd C (a' + 1) 1) (n + a') (by omega) hw (by omega)
            have hinD : (gateAt D a').inputs =
                [aliasWire (n + g) w (opnd C (a' + 1) 0), aliasWire (n + g) w (opnd C (a' + 1) 1)] := by
              rw [hgD]; simp [aliasGate, hab]
            rw [hal, W_and n D _ a' (by omega) (by rw [hgD]; exact ha_top.2.1) _ _ hinD h0D h1D,
              Bool.and_eq_true]
            exact ⟨hDp, hDq⟩
        exact erase_orR_mono C hA g w hg_lt hg_op hw (pairInput u v)
          (hbel_reach a ha_top.1 ha_top.2.2) hDa
  have hle := hL.2.2 D (IsAO2_of_AO n D hD_AO) hD_fun
  simp only [Circuit.size] at hle
  omega
lemma fin2_cases (b : Fin 2) : b = 0 ∨ b = 1 := by omega
open Classical in
lemma g_cone_gate_count {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g})
    (b : Fin 2) (T : Finset (Fin n)) (hT_sub : T ⊆ side (n := n) C g b)
    (hlam : ∀ h ∈ lam G C, ((orIn n C (n + h)) ∩ T).card ≤ 1) :
    T.card ≤ 1 + ((coneGates G C g).filter fun h => OrR n C (opnd C g b) (n + h)).card := by
  have hA : AO n C := AO_of_IsAO2 n C hL.1
  have hg_lt := (junk_single_props G C hL hT g hg).1
  obtain ⟨hb_lt, hb_noAnd⟩ := no_and_in_g_opnd G C hL hT g hg b
  have hR_lt : ∀ w ∈ ({opnd C g b} : Finset ℕ), w < n + C.gates.length := by
    intro w hw; rw [Finset.mem_singleton] at hw; subst hw; omega
  have hR_no : ∀ w ∈ ({opnd C g b} : Finset ℕ), ∀ h < C.gates.length,
      (gateAt C h).op = GateOp.and → ¬ OrR n C w (n + h) := by
    intro w hw; rw [Finset.mem_singleton] at hw; subst hw; exact hb_noAnd
  have hbound := or_dag_leaf_bound C hA T (lam G C) hlam {opnd C g b} hR_lt hR_no
  have hlhs : (({opnd C g b} : Finset ℕ).biUnion (fun w => orIn n C w) ∩ T) = T := by
    ext u
    simp only [Finset.mem_inter, Finset.mem_biUnion, Finset.mem_singleton, exists_eq_left]
    exact ⟨fun h => h.2, fun hu => ⟨hT_sub hu, hu⟩⟩
  rw [hlhs, Finset.card_singleton] at hbound
  have hF_sub : ((Finset.range C.gates.length).filter fun h =>
      (gateAt C h).op = GateOp.or ∧ h ∉ lam G C ∧ ∃ w ∈ ({opnd C g b} : Finset ℕ), OrR n C w (n + h)) ⊆
      (coneGates G C g).filter fun h => OrR n C (opnd C g b) (n + h) := by
    intro h hh
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton, exists_eq_left] at hh
    obtain ⟨hh_lt, hh_op, hh_notLam, hreach⟩ := hh
    obtain ⟨horN, hnotMix⟩ := pure_or_gate_in_orN_not_mixing G C hL (opnd C g b) (by omega)
      hb_noAnd h hh_lt hh_op hreach
    refine Finset.mem_filter.mpr ⟨?_, hreach⟩
    simp only [coneGates, Finset.mem_filter, Finset.mem_sdiff]
    refine ⟨⟨⟨horN, hh_notLam⟩, hnotMix⟩, ?_⟩
    have hre := orR_orReaches n C hA h hh_lt (opnd C g b) (by omega) hreach
    rcases fin2_cases b with rfl | rfl
    · exact Or.inl hre
    · exact Or.inr (Or.inl hre)
  exact hbound.trans (Nat.add_le_add_left (Finset.card_le_card hF_sub) 1)
open Classical in
lemma g_cones_disjoint {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g})
    (hdisj : side (n := n) C g 0 ∩ side (n := n) C g 1 = ∅) :
    Disjoint ((coneGates G C g).filter fun h => OrR n C (opnd C g 0) (n + h))
             ((coneGates G C g).filter fun h => OrR n C (opnd C g 1) (n + h)) := by
  have hA : AO n C := AO_of_IsAO2 n C hL.1
  have hg_lt := (junk_single_props G C hL hT g hg).1
  obtain ⟨h0_lt, h0_no⟩ := no_and_in_g_opnd G C hL hT g hg 0
  obtain ⟨h1_lt, h1_no⟩ := no_and_in_g_opnd G C hL hT g hg 1
  rw [Finset.disjoint_left]
  intro h hh0 hh1
  have hr0 := (Finset.mem_filter.mp hh0).2
  have hr1 := (Finset.mem_filter.mp hh1).2
  have hh_lt : h < C.gates.length := by
    have := orR_le n C hA _ _ hr0; omega
  have hne := (pure_or_wire_eval C hA (n + h) (by omega)
    (fun k hk hop hrk => h0_no k hk hop (hr0.trans hrk))).1
  obtain ⟨u, hu⟩ := hne
  have hru := (mem_orIn n C hA (n + h) (by omega) u).mp hu
  have hu0 : u ∈ side (n := n) C g 0 :=
    (mem_orIn n C hA (opnd C g 0) (by omega) u).mpr (hr0.trans hru)
  have hu1 : u ∈ side (n := n) C g 1 :=
    (mem_orIn n C hA (opnd C g 1) (by omega) u).mpr (hr1.trans hru)
  have : u ∈ side (n := n) C g 0 ∩ side (n := n) C g 1 := Finset.mem_inter.mpr ⟨hu0, hu1⟩
  rw [hdisj] at this
  exact Finset.notMem_empty u this
lemma ustar_ne_implies_mix_or_cl {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h4 : NoFourCycle G) (hE : G.edgeFinset.Nonempty)
    (hL : IsLeastAO G C) (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g})
    (hUne : (Ustar G C).Nonempty) :
    1 ≤ (mixing G C).card + 2 * (centreless G C).card := by
  obtain ⟨e, he⟩ := hUne
  induction e using Sym2.ind with
  | _ u v =>
    have huv : G.Adj u v := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp he).1
    obtain ⟨_, _, htri⟩ := ustar_edge_structure G C h4 hE hL hT g hg u v huv he
    rcases htri with ⟨a, haCL, _⟩ | ⟨_, _, _, _, _, m, hm, _⟩
    · have := Finset.card_pos.mpr ⟨a, haCL⟩; omega
    · have := Finset.card_pos.mpr ⟨m, hm⟩; omega
lemma g_pair_sides {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g})
    (u v : Fin n) (hgtrue : gateVal n C g (pairInput u v) = true) :
    (u ∈ side (n := n) C g 0 ∨ v ∈ side (n := n) C g 0) ∧
    (u ∈ side (n := n) C g 1 ∨ v ∈ side (n := n) C g 1) := by
  have hsem := (g_semantics G C hL hT g hg).2.2.1 (pairInput u v)
  rw [W_eq_gateVal] at hsem
  obtain ⟨⟨p, hp, hpu⟩, ⟨q, hq, hqu⟩⟩ := hsem.mp hgtrue
  rw [pairInput_true] at hpu hqu
  constructor
  · rcases hpu with rfl | rfl
    · exact Or.inl hp
    · exact Or.inr hp
  · rcases hqu with rfl | rfl
    · exact Or.inl hq
    · exact Or.inr hq
end Close


end PEqualNP.Outside.L_meta_2448_aux.foundation


namespace PEqualNP.Outside.L_meta_2448.cross
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

lemma wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

lemma wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

lemma getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

lemma wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

lemma gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

lemma getD_ofFn {n : ℕ} (f : Fin n → Bool) (i : Fin n) :
    (List.ofFn f).getD (i : ℕ) false = f i := by
  simp

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    PEqualNP.MetaComplexity.NestedCover.gateAt C k = C.gates[k] := by
  unfold PEqualNP.MetaComplexity.NestedCover.gateAt
  rw [List.getD_eq_getElem _ _ hk]

def cf (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) : List (List ℕ) :=
  gs.foldl (PEqualNP.EdgeOwnership.coneStep n) cs

lemma cf_append (n : ℕ) (a b : List Gate) (cs : List (List ℕ)) :
    cf n (a ++ b) cs = cf n b (cf n a cs) := by
  simp [cf, List.foldl_append]

lemma cf_cons (n : ℕ) (g : Gate) (gs : List Gate) (cs : List (List ℕ)) :
    cf n (g :: gs) cs = cf n gs (PEqualNP.EdgeOwnership.coneStep n cs g) := rfl

lemma cs_len (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    (PEqualNP.EdgeOwnership.coneStep n cs g).length = cs.length + 1 := by
  unfold PEqualNP.EdgeOwnership.coneStep; simp

lemma cf_len (n : ℕ) : ∀ (gs : List Gate) (cs : List (List ℕ)),
    (cf n gs cs).length = cs.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro cs; rfl
  | cons g gs ih =>
    intro cs
    rw [cf_cons, ih, cs_len, List.length_cons]; omega

lemma cf_keep (n : ℕ) : ∀ (gs : List Gate) (cs : List (List ℕ)) (j : ℕ), j < cs.length →
    (cf n gs cs).getD j [] = cs.getD j [] := by
  intro gs
  induction gs with
  | nil => intro cs j _; rfl
  | cons g gs ih =>
    intro cs j hj
    rw [cf_cons, ih _ j (by rw [cs_len]; omega)]
    unfold PEqualNP.EdgeOwnership.coneStep
    exact List.getD_append _ _ _ _ hj

lemma snocD (L : List (List ℕ)) (v : List ℕ) (j : ℕ) (h : L.length = j) :
    (L ++ [v]).getD j [] = v := by
  subst h; simp [List.getD_eq_getElem?_getD]

lemma cone_iff (n : ℕ) (gs : List Gate) (j : ℕ) (hj : j < gs.length) (i : ℕ) :
    i ∈ (cf n gs []).getD j [] ↔ ∃ w ∈ gs[j].inputs, n ≤ w ∧ w < n + j ∧
      (i = w - n ∨ i ∈ (cf n gs []).getD (w - n) []) := by
  have hP : (cf n (gs.take j) []).length = j := by
    rw [cf_len, List.length_take, Nat.min_eq_left (le_of_lt hj)]; simp
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  have e : cf n gs [] = cf n (gs.drop (j + 1))
      (PEqualNP.EdgeOwnership.coneStep n (cf n (gs.take j) []) gs[j]) := by
    conv_lhs => rw [hsplit]
    rw [cf_append, cf_cons]
  have hfull : ∀ m, m < j → (cf n gs []).getD m [] = (cf n (gs.take j) []).getD m [] := by
    intro m hm
    rw [e, cf_keep _ _ _ m (by rw [cs_len, hP]; omega)]
    unfold PEqualNP.EdgeOwnership.coneStep
    exact List.getD_append _ _ _ _ (by omega)
  have hj_eq : (cf n gs []).getD j [] =
      (gs[j].inputs.filter (fun w => decide (n ≤ w ∧ w < n + (cf n (gs.take j) []).length))).flatMap
        (fun w => (w - n) :: (cf n (gs.take j) []).getD (w - n) []) := by
    rw [e, cf_keep _ _ _ j (by rw [cs_len, hP]; omega)]
    unfold PEqualNP.EdgeOwnership.coneStep
    exact snocD _ _ j hP
  rw [hj_eq, List.mem_flatMap]
  constructor
  · rintro ⟨w, hw, hi⟩
    obtain ⟨hw1, hw2⟩ := List.mem_filter.1 hw
    have hw3 := of_decide_eq_true hw2
    rw [hP] at hw3
    refine ⟨w, hw1, hw3.1, hw3.2, ?_⟩
    rcases List.mem_cons.1 hi with h1 | h1
    · exact Or.inl h1
    · right; rw [hfull _ (by omega)]; exact h1
  · rintro ⟨w, hw1, hw2, hw3, hi⟩
    refine ⟨w, List.mem_filter.2 ⟨hw1, decide_eq_true (by rw [hP]; exact ⟨hw2, hw3⟩)⟩, ?_⟩
    rcases hi with h1 | h1
    · exact List.mem_cons.2 (Or.inl h1)
    · rw [hfull _ (by omega)] at h1
      exact List.mem_cons.2 (Or.inr h1)

lemma cone_lt (n : ℕ) (gs : List Gate) (i j : ℕ) (h : i ∈ (cf n gs []).getD j []) :
    j < gs.length := by
  by_contra hc
  rw [List.getD_eq_default _ _ (by rw [cf_len]; simp; omega)] at h
  cases h

open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover in
lemma valf (n : ℕ) (C : Circuit) (y : Fin n → Bool) (m : ℕ) (hm : m < C.gates.length) :
    gateVal n C m y = (C.gates[m]).op.eval
      (C.gates[m].inputs.map fun i => (wf (C.gates.take m) (List.ofFn y)).getD i false) := by
  have h := gate_val C.gates (List.ofFn y) m hm
  rw [List.length_ofFn] at h
  exact h

open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover in
lemma wire_reach (n : ℕ) (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C)
    (e : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (rec : ∀ j, j < k → (gateAt C j).op = GateOp.or → gateVal n C j e = true →
      (∀ i, InCone n C i j → (gateAt C i).op = GateOp.and → gateVal n C i e = false) →
      ∃ u : Fin n, e u = true ∧ ∀ y : Fin n → Bool, y u = true → gateVal n C j y = true)
    (hown : ∀ i, InCone n C i k → (gateAt C i).op = GateOp.and → gateVal n C i e = false)
    (i : ℕ) (hi : i ∈ C.gates[k].inputs)
    (hv : (wf (C.gates.take k) (List.ofFn e)).getD i false = true) :
    ∃ u : Fin n, e u = true ∧ ∀ y : Fin n → Bool, y u = true →
      (wf (C.gates.take k) (List.ofFn y)).getD i false = true := by
  have hik : i < n + k := by
    by_contra hge
    rw [List.getD_eq_default _ _ (by
      rw [wf_len, List.length_ofFn, List.length_take, Nat.min_eq_left (le_of_lt hk)]; omega)] at hv
    exact absurd hv (by decide)
  by_cases hin : i < n
  · refine ⟨⟨i, hin⟩, ?_, ?_⟩
    · rw [wf_keep _ _ i (by rw [List.length_ofFn]; exact hin)] at hv
      rw [← getD_ofFn e ⟨i, hin⟩]
      exact hv
    · intro y hy
      rw [wf_keep _ _ i (by rw [List.length_ofFn]; exact hin)]
      rw [← getD_ofFn y ⟨i, hin⟩] at hy
      exact hy
  · have hj : i - n < k := by omega
    have hjl : i - n < C.gates.length := by omega
    have hw : ∀ y : Fin n → Bool, (wf (C.gates.take k) (List.ofFn y)).getD i false
        = gateVal n C (i - n) y := by
      intro y
      rw [← wire_take C.gates (List.ofFn y) k i (by rw [List.length_ofFn]; exact hik) (le_of_lt hk)]
      show _ = (wf C.gates (List.ofFn y)).getD (n + (i - n)) false
      congr 1
      omega
    have hcone : InCone n C (i - n) k :=
      (cone_iff n C.gates k hk (i - n)).2 ⟨i, hi, by omega, hik, Or.inl rfl⟩
    have hop : (gateAt C (i - n)).op = GateOp.or := by
      rw [gateAt_eq C _ hjl]
      rcases (hC _ (List.getElem_mem hjl)).1 with h | h
      · exfalso
        have := hown (i - n) hcone (by rw [gateAt_eq C _ hjl]; exact h)
        rw [← hw e, hv] at this
        exact absurd this (by decide)
      · exact h
    obtain ⟨u, hu1, hu2⟩ := rec (i - n) hj hop (by rw [← hw e]; exact hv)
      (fun i' hc ha => hown i' ((cone_iff n C.gates k hk i').2 ⟨i, hi, by omega, hik, Or.inr hc⟩) ha)
    exact ⟨u, hu1, fun y hy => by rw [hw y]; exact hu2 y hy⟩

open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover in
lemma or_reach (n : ℕ) (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C)
    (e : Fin n → Bool) : ∀ m, m < C.gates.length → (gateAt C m).op = GateOp.or →
      gateVal n C m e = true →
      (∀ i, InCone n C i m → (gateAt C i).op = GateOp.and → gateVal n C i e = false) →
      ∃ u : Fin n, e u = true ∧ ∀ y : Fin n → Bool, y u = true → gateVal n C m y = true := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm hop hval hown
    rw [gateAt_eq C m hm] at hop
    have hv2 := hval
    rw [valf n C e m hm, hop] at hv2
    simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id] at hv2
    obtain ⟨i, hi, hiv⟩ := hv2
    obtain ⟨u, hu1, hu2⟩ := wire_reach n C hC e m hm
      (fun j hj h1 h2 h3 => ih j hj (lt_trans hj hm) h1 h2 h3) hown i hi hiv
    refine ⟨u, hu1, fun y hy => ?_⟩
    rw [valf n C y m hm, hop]
    simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact ⟨i, hi, hu2 y hy⟩

lemma cone_idx (n : ℕ) (gs : List Gate) : ∀ j i, i ∈ (cf n gs []).getD j [] → i < j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro i hc
    have hj := cone_lt n gs i j hc
    obtain ⟨w, _, hw1, hw2, hw3⟩ := (cone_iff n gs j hj i).1 hc
    rcases hw3 with e | e
    · omega
    · have := ih (w - n) (by omega) i e
      omega

lemma cross_nonedge : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [_x3 : DecidableRel x2.Adj], (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) → PEqualNP.TopForm.NoFourCycle x2 → ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 → ∀ (x8 : ℕ) (x9 x10 x11 x12 : Fin x1), x2.Adj x9 x10 → x2.Adj x11 x12 → PEqualNP.EdgeOwnership.Owns x1 x6 x8 x9 x10 → PEqualNP.EdgeOwnership.Owns x1 x6 x8 x11 x12 → x9 ≠ x11 → x9 ≠ x12 → x10 ≠ x11 → x10 ≠ x12 → ∃ (x21 : Fin x1) (x22 : Fin x1), (x21 = x9 ∨ x21 = x10) ∧ (x22 = x11 ∨ x22 = x12) ∧ ¬x2.Adj x21 x22 ∧ PEqualNP.EdgeOwnership.gateVal x1 x6 x8 (PEqualNP.EdgeOwnership.pairInput x21 x22) = Bool.true := by
  intro n G _ hT hNF C hC k p1 p2 q1 q2 hadj1 hadj2 hO1 hO2 h1 h2 h3 h4
  have pickQ : ∀ a : Fin n, ∃ b : Fin n, (b = q1 ∨ b = q2) ∧ ¬ G.Adj a b := by
    intro a
    by_contra hc
    push Not at hc
    exact hT q1 q2 a hadj2 (hc q2 (Or.inr rfl)).symm (hc q1 (Or.inl rfl))
  have pickP : ∀ b : Fin n, ∃ a : Fin n, (a = p1 ∨ a = p2) ∧ ¬ G.Adj a b := by
    intro b
    by_contra hc
    push Not at hc
    exact hT p1 p2 b hadj1 (hc p2 (Or.inr rfl)) (hc p1 (Or.inl rfl)).symm
  obtain ⟨hk, hop, hv1, hown1⟩ := hO1
  obtain ⟨_, _, hv2, hown2⟩ := hO2
  rw [gateAt_eq C k hk] at hop
  have hown1' : ∀ i, PEqualNP.EdgeOwnership.InCone n C i k →
      (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = GateOp.and →
      PEqualNP.EdgeOwnership.gateVal n C i (PEqualNP.EdgeOwnership.pairInput p1 p2) = false :=
    fun i hc ha => hown1 i (cone_idx n C.gates k i hc) hc ha
  have hown2' : ∀ i, PEqualNP.EdgeOwnership.InCone n C i k →
      (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = GateOp.and →
      PEqualNP.EdgeOwnership.gateVal n C i (PEqualNP.EdgeOwnership.pairInput q1 q2) = false :=
    fun i hc ha => hown2 i (cone_idx n C.gates k i hc) hc ha
  have hall : ∀ e : Fin n → Bool, PEqualNP.EdgeOwnership.gateVal n C k e = true →
      ∀ i ∈ C.gates[k].inputs, (wf (C.gates.take k) (List.ofFn e)).getD i false = true := by
    intro e he i hi
    rw [valf n C e k hk, hop] at he
    simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id] at he
    exact he i hi
  have reach1 : ∀ i ∈ C.gates[k].inputs, ∃ u : Fin n, (u = p1 ∨ u = p2) ∧ ∀ y : Fin n → Bool,
      y u = true → (wf (C.gates.take k) (List.ofFn y)).getD i false = true := by
    intro i hi
    obtain ⟨u, hu1, hu2⟩ := wire_reach n C hC _ k hk
      (fun j hj a b c => or_reach n C hC _ j (lt_trans hj hk) a b c) hown1' i hi (hall _ hv1 i hi)
    exact ⟨u, of_decide_eq_true hu1, hu2⟩
  have reach2 : ∀ i ∈ C.gates[k].inputs, ∃ u : Fin n, (u = q1 ∨ u = q2) ∧ ∀ y : Fin n → Bool,
      y u = true → (wf (C.gates.take k) (List.ofFn y)).getD i false = true := by
    intro i hi
    obtain ⟨u, hu1, hu2⟩ := wire_reach n C hC _ k hk
      (fun j hj a b c => or_reach n C hC _ j (lt_trans hj hk) a b c) hown2' i hi (hall _ hv2 i hi)
    exact ⟨u, of_decide_eq_true hu1, hu2⟩
  have gtrue : ∀ y : Fin n → Bool,
      (∀ i ∈ C.gates[k].inputs, (wf (C.gates.take k) (List.ofFn y)).getD i false = true) →
      PEqualNP.EdgeOwnership.gateVal n C k y = true := by
    intro y hy
    rw [valf n C y k hk, hop]
    simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact hy
  have pl : ∀ a b : Fin n, PEqualNP.EdgeOwnership.pairInput a b a = true :=
    fun a b => decide_eq_true (Or.inl rfl)
  have pr : ∀ a b : Fin n, PEqualNP.EdgeOwnership.pairInput a b b = true :=
    fun a b => decide_eq_true (Or.inr rfl)
  have hlen := (hC _ (List.getElem_mem hk)).2
  match hin : C.gates[k].inputs, hlen with
  | [], _ =>
    obtain ⟨b, hb1, hb2⟩ := pickQ p1
    refine ⟨p1, b, Or.inl rfl, hb1, hb2, gtrue _ ?_⟩
    intro i hi
    rw [hin] at hi
    cases hi
  | [i1], _ =>
    obtain ⟨u, hu0, hu⟩ := reach1 i1 (by rw [hin]; simp)
    obtain ⟨b, hb1, hb2⟩ := pickQ u
    refine ⟨u, b, hu0, hb1, hb2, gtrue _ ?_⟩
    intro i hi
    rw [hin] at hi
    rw [List.mem_singleton.1 hi]
    exact hu _ (pl u b)
  | [i1, i2], _ =>
    obtain ⟨u1, hu1, hU1⟩ := reach1 i1 (by rw [hin]; simp)
    obtain ⟨u2, hu2, hU2⟩ := reach1 i2 (by rw [hin]; simp)
    obtain ⟨w1, hw1, hW1⟩ := reach2 i1 (by rw [hin]; simp)
    obtain ⟨w2, hw2, hW2⟩ := reach2 i2 (by rw [hin]; simp)
    have two : ∀ (a b : Fin n) (y : Fin n → Bool), y a = true → y b = true →
        (∀ z : Fin n → Bool, z a = true → (wf (C.gates.take k) (List.ofFn z)).getD i1 false = true) →
        (∀ z : Fin n → Bool, z b = true → (wf (C.gates.take k) (List.ofFn z)).getD i2 false = true) →
        PEqualNP.EdgeOwnership.gateVal n C k y = true := by
      intro a b y ha hb hA hB
      apply gtrue
      intro i hi
      rw [hin] at hi
      rcases List.mem_pair.1 hi with e | e
      · rw [e]; exact hA y ha
      · rw [e]; exact hB y hb
    by_cases c1 : G.Adj u1 w2
    swap
    · exact ⟨u1, w2, hu1, hw2, c1, two u1 w2 _ (pl _ _) (pr _ _) hU1 hW2⟩
    by_cases c2 : G.Adj w1 u2
    swap
    · exact ⟨u2, w1, hu2, hw1, fun h => c2 h.symm, two w1 u2 (PEqualNP.EdgeOwnership.pairInput u2 w1) (pr _ _) (pl _ _) hW1 hU2⟩
    by_cases c3 : u1 = u2
    · obtain ⟨b, hb1, hb2⟩ := pickQ u1
      exact ⟨u1, b, hu1, hb1, hb2, two u1 u1 (PEqualNP.EdgeOwnership.pairInput u1 b) (pl _ _) (pl _ _) hU1 (c3 ▸ hU2)⟩
    by_cases c4 : w1 = w2
    · obtain ⟨a, ha1, ha2⟩ := pickP w1
      exact ⟨a, w1, ha1, hw1, ha2, two w1 w1 (PEqualNP.EdgeOwnership.pairInput a w1) (pr _ _) (pr _ _) hW1 (c4 ▸ hW2)⟩
    exfalso
    have a12 : G.Adj u1 u2 := by
      rcases hu1 with e1 | e1 <;> rcases hu2 with e2 | e2
      · exact absurd (e1.trans e2.symm) c3
      · rw [e1, e2]; exact hadj1
      · rw [e1, e2]; exact hadj1.symm
      · exact absurd (e1.trans e2.symm) c3
    have b12 : G.Adj w1 w2 := by
      rcases hw1 with e1 | e1 <;> rcases hw2 with e2 | e2
      · exact absurd (e1.trans e2.symm) c4
      · rw [e1, e2]; exact hadj2
      · rw [e1, e2]; exact hadj2.symm
      · exact absurd (e1.trans e2.symm) c4
    have hne : u1 ≠ w1 := by
      rcases hu1 with e1 | e1 <;> rcases hw1 with e2 | e2 <;> rw [e1, e2]
      · exact h1
      · exact h2
      · exact h3
      · exact h4
    have hne2 : u2 ≠ w2 := by
      rcases hu2 with e1 | e1 <;> rcases hw2 with e2 | e2 <;> rw [e1, e2]
      · exact h1
      · exact h2
      · exact h3
      · exact h4
    have hcard := hNF u1 w1 hne
    have : 1 < (Finset.univ.filter fun w => G.Adj u1 w ∧ G.Adj w1 w).card :=
      Finset.one_lt_card.2 ⟨u2, Finset.mem_filter.2 ⟨Finset.mem_univ _, a12, c2⟩,
        w2, Finset.mem_filter.2 ⟨Finset.mem_univ _, c1, b12⟩, hne2⟩
    omega
  | _ :: _ :: _ :: _, h => exact absurd h (by simp)

open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

lemma star_of_proper_pair_sound (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (htri : ∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hfour : PEqualNP.TopForm.NoFourCycle G)
    (hm : Monotone2 C)
    (hclean : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∀ u v : Fin n, u ≠ v → gateVal n C j (pairInput u v) = true → G.Adj u v) :
    HasStarProfile n G C := by
  classical
  intro j hj hjand
  have hmeet (u v p q : Fin n) (huv : G.Adj u v) (hpq : G.Adj p q)
      (h1 : Owns n C j u v) (h2 : Owns n C j p q) :
      u = p ∨ u = q ∨ v = p ∨ v = q := by
    by_contra hn
    push Not at hn
    obtain ⟨a, b, ha, hb, hab, hval⟩ :=
      cross_nonedge n G htri hfour C hm j u v p q huv hpq h1 h2 hn.1 hn.2.1 hn.2.2.1 hn.2.2.2
    have hne : a ≠ b := by
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> tauto
    exact hab (hclean j hj hjand a b hne hval)
  by_cases used : ∃ a b, G.Adj a b ∧ Owns n C j a b
  · right
    obtain ⟨a, b, hab, hoab⟩ := used
    by_cases ha : ∀ u v : Fin n, G.Adj u v → Owns n C j u v → u = a ∨ v = a
    · exact ⟨a, ha⟩
    · push Not at ha
      obtain ⟨p, q, hpq, hopq, hpa, hqa⟩ := ha
      have hbpq : p = b ∨ q = b := by
        have h := hmeet p q a b hpq hab hopq hoab
        tauto
      have hext : ∃ w : Fin n, w ≠ a ∧ G.Adj b w ∧
          ∀ u v : Fin n, G.Adj u v → Owns n C j u v → u = b ∨ v = b ∨ u = w ∨ v = w := by
        rcases hbpq with rfl | rfl
        · refine ⟨q, hqa, hpq, ?_⟩
          intro u v huv hov
          have h := hmeet u v p q huv hpq hov hopq
          tauto
        · refine ⟨p, hpa, hpq.symm, ?_⟩
          intro u v huv hov
          have h := hmeet u v p q huv hpq hov hopq
          tauto
      obtain ⟨w, hwa, hbw, hmeetw⟩ := hext
      refine ⟨b, ?_⟩
      intro u v huv hov
      by_contra hn
      push Not at hn
      have huva : u = a ∨ v = a := by
        have h := hmeet u v a b huv hab hov hoab
        tauto
      have huvw : u = w ∨ v = w := by
        have h := hmeetw u v huv hov
        tauto
      have hwaAdj : G.Adj w a := by
        rcases huva with h | h
        · subst u
          have hvw : v = w := huvw.resolve_left (Ne.symm hwa)
          simpa [hvw] using huv.symm
        · subst v
          have huw : u = w := huvw.resolve_right (Ne.symm hwa)
          simpa [huw] using huv
      exact htri a b w hab hbw hwaAdj
  · left
    exact fun u v huv ho => used ⟨u, v, huv, ho⟩

open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

lemma owns_primary_input {n : ℕ} (C : Circuit) (j : ℕ) (a : Fin n)
    (ha : a.val ∈ (gateAt C j).inputs) {u v : Fin n} (ho : Owns n C j u v) :
    u = a ∨ v = a := by
  obtain ⟨hj, hop, hv, _⟩ := ho
  rw [gateAt_eq C j hj] at ha hop
  rw [valf n C (pairInput u v) j hj, hop] at hv
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id] at hv
  have he := hv a.val ha
  rw [wf_keep _ _ a.val (by simp), getD_ofFn] at he
  have ha' : a = u ∨ a = v := of_decide_eq_true he
  exact ha'.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)

lemma star_of_primary_operands {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (ha : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∃ a : Fin n, a.val ∈ (gateAt C j).inputs) :
    HasStarProfile n G C := by
  intro j hj hop
  obtain ⟨a, hmem⟩ := ha j hj hop
  right
  refine ⟨a, ?_⟩
  intro u v _ ho
  exact owns_primary_input C j a hmem ho

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

end PEqualNP.Outside.L_meta_2448.cross


namespace PEqualNP.Outside.L_meta_2448_aux.oneJunk

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_2448_aux.foundation PEqualNP.Outside.L_meta_2448_aux.foundation.Close
open PEqualNP.Outside.L_meta_2448_aux.foundation.M1528.P1.S98 (W AO AO_of_IsAO2 W_and W_input)
open PEqualNP.Outside.L_meta_2448_aux.foundation.M1528.P2 (OrR mem_orIn orR_mono opnd_eq graphFun_pair orR_orReaches orR_le orR_cone pairInput_true)

lemma cover_of_budget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g : ℕ) (K : Finset (Fin n))
    (hKcov : ∀ e ∈ starEdges G C, ∃ v ∈ K, v ∈ e)
    (h1528 : G.edgeFinset.card + K.card + (pen G C g K).card + 1 +
      (mixing G C).card + 2 * (centreless G C).card + (coneGates G C g).card ≤
      C.size + (Ustar G C).card + 1)
    (X0 : Finset (Fin n))
    (hXcov : ∀ e ∈ Ustar G C, ∃ v ∈ K ∪ X0, v ∈ e)
    (hbudget : (Ustar G C).card + (X0 \ K).card ≤
      (pen G C g K).card + (mixing G C).card + 2 * (centreless G C).card +
        (coneGates G C g).card + 1) :
    ∃ T : Finset (Fin n), (∀ e ∈ G.edgeFinset, ∃ v ∈ T, v ∈ e) ∧
      G.edgeFinset.card + T.card ≤ C.size + 1 := by
  classical
  have hfull : ∀ e ∈ G.edgeFinset, ∃ v ∈ K ∪ (X0 \ K), v ∈ e := by
    intro e he
    by_cases hS : e ∈ starEdges G C
    · obtain ⟨v, hv, hve⟩ := hKcov e hS
      exact ⟨v, Finset.mem_union_left _ hv, hve⟩
    · have hU : e ∈ Ustar G C := Finset.mem_sdiff.mpr ⟨he, hS⟩
      obtain ⟨v, hv, hve⟩ := hXcov e hU
      have hv' : v ∈ K ∪ (X0 \ K) := by
        rcases Finset.mem_union.mp hv with hvK | hvX
        · exact Finset.mem_union_left _ hvK
        · by_cases h : v ∈ K
          · exact Finset.mem_union_left _ h
          · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hvX, h⟩)
      exact ⟨v, hv', hve⟩
  refine ⟨K ∪ (X0 \ K), hfull, ?_⟩
  have hcard : (K ∪ (X0 \ K)).card = K.card + (X0 \ K).card :=
    Finset.card_union_of_disjoint Finset.disjoint_sdiff
  omega

lemma one_center {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g : ℕ) (K : Finset (Fin n))
    (hKcov : ∀ e ∈ starEdges G C, ∃ v ∈ K, v ∈ e)
    (h1528 : G.edgeFinset.card + K.card + (pen G C g K).card + 1 +
      (mixing G C).card + 2 * (centreless G C).card + (coneGates G C g).card ≤
      C.size + (Ustar G C).card + 1)
    (h4 : NoFourCycle G) (hE : G.edgeFinset.Nonempty)
    (hL : IsLeastAO G C) (hT : TopForm G C) (hg : junk G C = {g})
    (hUne : (Ustar G C).Nonempty)
    (hdisj : side (n := n) C g 0 ∩ side (n := n) C g 1 = ∅)
    (b : Fin 2) (zstar : Fin n) (hz_side : zstar ∈ side (n := n) C g b)
    (hU_inc : ∀ e ∈ Ustar G C, zstar ∈ e) :
    ∃ T : Finset (Fin n), (∀ e ∈ G.edgeFinset, ∃ v ∈ T, v ∈ e) ∧
      G.edgeFinset.card + T.card ≤ C.size + 1 := by
  classical
  let PU := (side (n := n) C g (1 - b)).filter fun p => s(p, zstar) ∈ Ustar G C
  have hU_eq : Ustar G C = PU.image (fun p => s(p, zstar)) := by
    ext e
    induction e using Sym2.ind with
    | _ u v =>
      simp only [Finset.mem_image, PU, Finset.mem_filter]
      constructor
      · intro hU
        have huv : G.Adj u v := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp hU).1
        have hz_in := hU_inc s(u, v) hU
        obtain ⟨hgtrue, _, _⟩ := ustar_edge_structure G C h4 hE hL hT g hg u v huv hU
        obtain ⟨h0, h1⟩ := g_pair_sides G C hL hT g hg u v hgtrue
        have h1b : u ∈ side (n := n) C g (1 - b) ∨ v ∈ side (n := n) C g (1 - b) := by
          fin_cases b <;> [exact h1; exact h0]
        have hz_not_1b : zstar ∉ side (n := n) C g (1 - b) := by
          intro hmem
          have : zstar ∈ side (n := n) C g 0 ∩ side (n := n) C g 1 := by
            fin_cases b
            · exact Finset.mem_inter.mpr ⟨hz_side, hmem⟩
            · exact Finset.mem_inter.mpr ⟨hmem, hz_side⟩
          rw [hdisj] at this; exact Finset.notMem_empty _ this
        rcases Sym2.mem_iff.mp hz_in with rfl | rfl
        · rcases h1b with hu | hv
          · exact absurd hu hz_not_1b
          · exact ⟨v, ⟨hv, by rw [Sym2.eq_swap]; exact hU⟩, Sym2.eq_swap⟩
        · rcases h1b with hu | hv
          · exact ⟨u, ⟨hu, hU⟩, rfl⟩
          · exact absurd hv hz_not_1b
      · rintro ⟨p, ⟨_, hU⟩, heq⟩; rwa [← heq]
  have hPU_adj : ∀ p ∈ PU, G.Adj zstar p := by
    intro p hp
    exact (SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp hp).2).1).symm
  have hU_card : (Ustar G C).card = PU.card := by
    rw [hU_eq, Finset.card_image_of_injOn]
    intro p1 hp1 p2 hp2 heq
    have hadj := hPU_adj p1 hp1
    rcases Sym2.eq_iff.mp heq with ⟨h, _⟩ | ⟨h, _⟩
    · exact h
    · exact absurd h hadj.ne'
  have hPU_notStar : ∀ p ∈ PU, s(zstar, p) ∉ starEdges G C := fun p hp => by
    rw [Sym2.eq_swap]; exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hp).2).2
  let Cg1b := (coneGates G C g).filter fun h => OrR n C (opnd C g (1 - b)) (n + h)
  have hCg_le : Cg1b.card ≤ (coneGates G C g).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hlamPU : ∀ h ∈ lam G C, ((orIn n C (n + h)) ∩ PU).card ≤ 1 :=
    lam_card_le_one_of_common_nbr G h4 C hL zstar PU hPU_adj (fun a _ ha _ _ => Or.inl (hPU_notStar a ha))
  have hcg1b : PU.card ≤ 1 + Cg1b.card :=
    g_cone_gate_count G C hL hT g hg (1 - b) PU (Finset.filter_subset _ _) hlamPU
  have hXcov : ∀ e ∈ Ustar G C, ∃ v ∈ K ∪ {zstar}, v ∈ e :=
    fun e he => ⟨zstar, Finset.mem_union_right _ (Finset.mem_singleton_self _), hU_inc e he⟩
  have hmixcl := ustar_ne_implies_mix_or_cl G C h4 hE hL hT g hg hUne
  have hxcard : (({zstar} : Finset (Fin n)) \ K).card ≤ 1 :=
    (Finset.card_le_card Finset.sdiff_subset).trans (by simp)
  apply cover_of_budget G C g K hKcov h1528 {zstar} hXcov
  omega

lemma two_centers {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g : ℕ) (K : Finset (Fin n))
    (hKcov : ∀ e ∈ starEdges G C, ∃ v ∈ K, v ∈ e)
    (h1528 : G.edgeFinset.card + K.card + (pen G C g K).card + 1 +
      (mixing G C).card + 2 * (centreless G C).card + (coneGates G C g).card ≤
      C.size + (Ustar G C).card + 1)
    (h4 : NoFourCycle G) (hE : G.edgeFinset.Nonempty)
    (hL : IsLeastAO G C) (hT : TopForm G C) (hg : junk G C = {g})
    (hUne : (Ustar G C).Nonempty)
    (hdisj : side (n := n) C g 0 ∩ side (n := n) C g 1 = ∅)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hP2 : 2 ≤ (side (n := n) C g 0).card) (hQ2 : 2 ≤ (side (n := n) C g 1).card)
    (pstar qstar : Fin n)
    (hpW : pstar ∈ wmax G C g) (hpP : pstar ∈ side (n := n) C g 0)
    (hqW : qstar ∈ wmax G C g) (hqQ : qstar ∈ side (n := n) C g 1)
    (hp1_ex : ∃ p1 ∈ side (n := n) C g 0, p1 ≠ pstar ∧ s(p1, qstar) ∈ Ustar G C)
    (hq1_ex : ∃ q1 ∈ side (n := n) C g 1, q1 ≠ qstar ∧ s(pstar, q1) ∈ Ustar G C) :
    ∃ T : Finset (Fin n), (∀ e ∈ G.edgeFinset, ∃ v ∈ T, v ∈ e) ∧
      G.edgeFinset.card + T.card ≤ C.size + 1 := by
  classical
  have hA : AO n C := AO_of_IsAO2 n C hL.1
  have hg_lt := (junk_single_props G C hL hT g hg).1
  obtain ⟨_, _, _, hW_iff, pb, hpbP, qb, hqbQ, hbad_nadj⟩ := g_semantics G C hL hT g hg
  have h1529 := thm_1529 n G h4 (side (n := n) C g 0) (side (n := n) C g 1) (wmax G C g) hW_iff
  have h1530 := thm_1530 n G h4 (side (n := n) C g 0) (side (n := n) C g 1) (wmax G C g) hW_iff
  have hp_adj_Q : ∀ q ∈ side (n := n) C g 1, G.Adj pstar q := (h1529.1 pstar hpW hpP).2
  have hq_adj_P : ∀ p ∈ side (n := n) C g 0, G.Adj qstar p := (h1529.2.1 qstar hqW hqQ).2
  have hpq_adj : G.Adj pstar qstar := hp_adj_Q qstar hqQ
  have hWP_eq : wmax G C g ∩ side (n := n) C g 0 = {pstar} :=
    Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_inter.mpr ⟨hpW, hpP⟩, fun x hx =>
      Finset.card_le_one.mp (h1530.1 hQ2) x hx pstar (Finset.mem_inter.mpr ⟨hpW, hpP⟩)⟩
  have hWQ_eq : wmax G C g ∩ side (n := n) C g 1 = {qstar} :=
    Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_inter.mpr ⟨hqW, hqQ⟩, fun x hx =>
      Finset.card_le_one.mp (h1530.2.1 hP2) x hx qstar (Finset.mem_inter.mpr ⟨hqW, hqQ⟩)⟩
  have hP_notW : ∀ p ∈ side (n := n) C g 0, p ≠ pstar → p ∉ wmax G C g := by
    intro p hpP' hne hpW'
    have : p ∈ wmax G C g ∩ side (n := n) C g 0 := Finset.mem_inter.mpr ⟨hpW', hpP'⟩
    rw [hWP_eq, Finset.mem_singleton] at this; exact hne this
  have hQ_notW : ∀ q ∈ side (n := n) C g 1, q ≠ qstar → q ∉ wmax G C g := by
    intro q hqQ' hne hqW'
    have : q ∈ wmax G C g ∩ side (n := n) C g 1 := Finset.mem_inter.mpr ⟨hqW', hqQ'⟩
    rw [hWQ_eq, Finset.mem_singleton] at this; exact hne this
  let PU' := (side (n := n) C g 0).filter fun p => p ≠ pstar ∧ s(p, qstar) ∈ Ustar G C
  let QU' := (side (n := n) C g 1).filter fun q => q ≠ qstar ∧ s(pstar, q) ∈ Ustar G C
  have hU_class : ∀ e ∈ Ustar G C, e = s(pstar, qstar) ∨
      (∃ p ∈ PU', e = s(p, qstar)) ∨ (∃ q ∈ QU', e = s(pstar, q)) := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
      have huv : G.Adj u v := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp he).1
      obtain ⟨hgtrue, huvW, _⟩ := ustar_edge_structure G C h4 hE hL hT g hg u v huv he
      obtain ⟨h0, h1⟩ := g_pair_sides G C hL hT g hg u v hgtrue
      have hPQ : (u ∈ side (n := n) C g 0 ∧ v ∈ side (n := n) C g 1) ∨
                 (v ∈ side (n := n) C g 0 ∧ u ∈ side (n := n) C g 1) := by
        rcases h0 with hu0 | hv0 <;> rcases h1 with hu1 | hv1
        · exfalso; have : u ∈ side (n := n) C g 0 ∩ side (n := n) C g 1 := Finset.mem_inter.mpr ⟨hu0, hu1⟩
          rw [hdisj] at this; exact Finset.notMem_empty _ this
        · exact Or.inl ⟨hu0, hv1⟩
        · exact Or.inr ⟨hv0, hu1⟩
        · exfalso; have : v ∈ side (n := n) C g 0 ∩ side (n := n) C g 1 := Finset.mem_inter.mpr ⟨hv0, hv1⟩
          rw [hdisj] at this; exact Finset.notMem_empty _ this
      rcases hPQ with ⟨huP, hvQ⟩ | ⟨hvP, huQ⟩
      · rcases huvW with huW | hvW
        · have hup : u = pstar := by
            have : u ∈ wmax G C g ∩ side (n := n) C g 0 := Finset.mem_inter.mpr ⟨huW, huP⟩
            rwa [hWP_eq, Finset.mem_singleton] at this
          subst hup
          by_cases hvq : v = qstar
          · subst hvq; exact Or.inl rfl
          · exact Or.inr (Or.inr ⟨v, Finset.mem_filter.mpr ⟨hvQ, hvq, he⟩, rfl⟩)
        · have hvq : v = qstar := by
            have : v ∈ wmax G C g ∩ side (n := n) C g 1 := Finset.mem_inter.mpr ⟨hvW, hvQ⟩
            rwa [hWQ_eq, Finset.mem_singleton] at this
          subst hvq
          by_cases hup : u = pstar
          · subst hup; exact Or.inl rfl
          · exact Or.inr (Or.inl ⟨u, Finset.mem_filter.mpr ⟨huP, hup, he⟩, rfl⟩)
      · rcases huvW with huW | hvW
        · have huq : u = qstar := by
            have : u ∈ wmax G C g ∩ side (n := n) C g 1 := Finset.mem_inter.mpr ⟨huW, huQ⟩
            rwa [hWQ_eq, Finset.mem_singleton] at this
          subst huq
          by_cases hvp : v = pstar
          · subst hvp; exact Or.inl Sym2.eq_swap
          · exact Or.inr (Or.inl ⟨v, Finset.mem_filter.mpr ⟨hvP, hvp, by rw [Sym2.eq_swap]; exact he⟩, Sym2.eq_swap⟩)
        · have hvp : v = pstar := by
            have : v ∈ wmax G C g ∩ side (n := n) C g 0 := Finset.mem_inter.mpr ⟨hvW, hvP⟩
            rwa [hWP_eq, Finset.mem_singleton] at this
          subst hvp
          by_cases huq : u = qstar
          · subst huq; exact Or.inl Sym2.eq_swap
          · exact Or.inr (Or.inr ⟨u, Finset.mem_filter.mpr ⟨huQ, huq, by rw [Sym2.eq_swap]; exact he⟩, Sym2.eq_swap⟩)
  let EP := PU'.image (fun p => s(p, qstar))
  let EQ := QU'.image (fun q => s(pstar, q))
  have hEP_card : EP.card = PU'.card := by
    rw [Finset.card_image_of_injOn]
    intro p1 hp1 p2 hp2 heq
    have hadj := hq_adj_P p1 (Finset.mem_filter.mp hp1).1
    rcases Sym2.eq_iff.mp heq with ⟨h, _⟩ | ⟨h, _⟩
    · exact h
    · exact absurd h hadj.ne'
  have hEQ_card : EQ.card = QU'.card := by
    rw [Finset.card_image_of_injOn]
    intro q1 hq1 q2 hq2 heq
    have hadj := hp_adj_Q q1 (Finset.mem_filter.mp hq1).1
    rcases Sym2.eq_iff.mp heq with ⟨_, h⟩ | ⟨_, h⟩
    · exact h
    · exact absurd h.symm hadj.ne
  have hEP_EQ_disj : Disjoint EP EQ := by
    rw [Finset.disjoint_left]
    intro e h1 h2
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h1
    obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp h2
    have hp_ne := (Finset.mem_filter.mp hp).2.1
    have hq_ne := (Finset.mem_filter.mp hq).2.1
    rcases Sym2.eq_iff.mp heq with ⟨h, _⟩ | ⟨_, h⟩
    · exact hp_ne h.symm
    · exact hp_ne (by
        have : p ∈ side (n := n) C g 0 ∩ side (n := n) C g 1 :=
          Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hp).1, h ▸ (Finset.mem_filter.mp hq).1⟩
        rw [hdisj] at this; exact (Finset.notMem_empty _ this).elim)
  have hspq_notEP : s(pstar, qstar) ∉ EP := by
    intro h
    obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp h
    have hp_ne := (Finset.mem_filter.mp hp).2.1
    rcases Sym2.eq_iff.mp heq with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hp_ne h1
    · have : p ∈ side (n := n) C g 0 ∩ side (n := n) C g 1 :=
        Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hp).1, h1 ▸ hqQ⟩
      rw [hdisj] at this; exact Finset.notMem_empty _ this
  have hspq_notEQ : s(pstar, qstar) ∉ EQ := by
    intro h
    obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp h
    have hq_ne := (Finset.mem_filter.mp hq).2.1
    rcases Sym2.eq_iff.mp heq with ⟨_, h1⟩ | ⟨_, h1⟩
    · exact hq_ne h1
    · have : q ∈ side (n := n) C g 0 ∩ side (n := n) C g 1 :=
        Finset.mem_inter.mpr ⟨h1 ▸ hpP, (Finset.mem_filter.mp hq).1⟩
      rw [hdisj] at this; exact Finset.notMem_empty _ this
  let Cg0 := (coneGates G C g).filter fun h => OrR n C (opnd C g 0) (n + h)
  let Cg1 := (coneGates G C g).filter fun h => OrR n C (opnd C g 1) (n + h)
  have hCg_disj : Disjoint Cg0 Cg1 := g_cones_disjoint G C hL hT g hg hdisj
  have hCg_sum : Cg0.card + Cg1.card ≤ (coneGates G C g).card := by
    rw [← Finset.card_union_of_disjoint hCg_disj]
    exact Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
  have hCg0_lb : PU'.card ≤ Cg0.card := by
    let TP := insert pstar PU'
    have hp_not : pstar ∉ PU' := fun h => (Finset.mem_filter.mp h).2.1 rfl
    have hTP_sub : TP ⊆ side (n := n) C g 0 := by
      intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hp'
      · exact hpP
      · exact (Finset.mem_filter.mp hp').1
    have hlamTP : ∀ h ∈ lam G C, ((orIn n C (n + h)) ∩ TP).card ≤ 1 := by
      refine lam_card_le_one_of_common_nbr G h4 C hL qstar TP (fun p hp => hq_adj_P p (hTP_sub hp)) ?_
      intro u v hu hv huv
      rcases Finset.mem_insert.mp hu with rfl | hu'
      · rcases Finset.mem_insert.mp hv with rfl | hv'
        · exact absurd rfl huv
        · exact Or.inr (by rw [Sym2.eq_swap]; exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hv').2.2).2)
      · exact Or.inl (by rw [Sym2.eq_swap]; exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hu').2.2).2)
    have h : TP.card ≤ 1 + Cg0.card := g_cone_gate_count G C hL hT g hg 0 TP hTP_sub hlamTP
    rw [Finset.card_insert_of_notMem hp_not] at h
    omega
  have hCg1_lb : QU'.card ≤ Cg1.card := by
    let TQ := insert qstar QU'
    have hq_not : qstar ∉ QU' := fun h => (Finset.mem_filter.mp h).2.1 rfl
    have hTQ_sub : TQ ⊆ side (n := n) C g 1 := by
      intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hq'
      · exact hqQ
      · exact (Finset.mem_filter.mp hq').1
    have hlamTQ : ∀ h ∈ lam G C, ((orIn n C (n + h)) ∩ TQ).card ≤ 1 := by
      refine lam_card_le_one_of_common_nbr G h4 C hL pstar TQ (fun q hq => hp_adj_Q q (hTQ_sub hq)) ?_
      intro u v hu hv huv
      rcases Finset.mem_insert.mp hu with rfl | hu'
      · rcases Finset.mem_insert.mp hv with rfl | hv'
        · exact absurd rfl huv
        · exact Or.inr (Finset.mem_sdiff.mp (Finset.mem_filter.mp hv').2.2).2
      · exact Or.inl (Finset.mem_sdiff.mp (Finset.mem_filter.mp hu').2.2).2
    have h : TQ.card ≤ 1 + Cg1.card := g_cone_gate_count G C hL hT g hg 1 TQ hTQ_sub hlamTQ
    rw [Finset.card_insert_of_notMem hq_not] at h
    omega
  have hXcov : ∀ e ∈ Ustar G C, ∃ v ∈ K ∪ {pstar, qstar}, v ∈ e := by
    intro e he
    rcases hU_class e he with rfl | ⟨p, _, rfl⟩ | ⟨q, _, rfl⟩
    · exact ⟨pstar, Finset.mem_union_right _ (by simp), Sym2.mem_mk_left _ _⟩
    · exact ⟨qstar, Finset.mem_union_right _ (by simp), Sym2.mem_mk_right _ _⟩
    · exact ⟨pstar, Finset.mem_union_right _ (by simp), Sym2.mem_mk_left _ _⟩
  have hxcard : (({pstar, qstar} : Finset (Fin n)) \ K).card ≤ 2 :=
    (Finset.card_le_card Finset.sdiff_subset).trans Finset.card_le_two
  have hmixcl := ustar_ne_implies_mix_or_cl G C h4 hE hL hT g hg hUne
  apply cover_of_budget G C g K hKcov h1528 {pstar, qstar} hXcov
  by_cases hspqU : s(pstar, qstar) ∈ Ustar G C
  ·
    have hU_eq : Ustar G C = insert s(pstar, qstar) (EP ∪ EQ) := by
      ext e
      simp only [Finset.mem_insert, Finset.mem_union, EP, EQ, Finset.mem_image]
      constructor
      · intro he
        rcases hU_class e he with h | ⟨p, hp, rfl⟩ | ⟨q, hq, rfl⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl ⟨p, hp, rfl⟩)
        · exact Or.inr (Or.inr ⟨q, hq, rfl⟩)
      · rintro (rfl | ⟨p, hp, rfl⟩ | ⟨q, hq, rfl⟩)
        · exact hspqU
        · exact (Finset.mem_filter.mp hp).2.2
        · exact (Finset.mem_filter.mp hq).2.2
    have hU_card : (Ustar G C).card = PU'.card + QU'.card + 1 := by
      rw [hU_eq, Finset.card_insert_of_notMem (by simp [hspq_notEP, hspq_notEQ]),
        Finset.card_union_of_disjoint hEP_EQ_disj, hEP_card, hEQ_card]
    have hweight : 2 ≤ (mixing G C).card + 2 * (centreless G C).card := by
      by_cases hcl : 0 < (centreless G C).card
      · omega
      have hCL0 : (centreless G C).card = 0 := by omega
      obtain ⟨p1, hp1P, hp1_ne, hp1U⟩ := hp1_ex
      obtain ⟨q1, hq1Q, hq1_ne, hq1U⟩ := hq1_ex
      obtain ⟨_, _, htri_p⟩ := ustar_edge_structure G C h4 hE hL hT g hg p1 qstar
        (hq_adj_P p1 hp1P).symm hp1U
      rcases htri_p with ⟨a, haCL, _⟩ | ⟨a_p, ha_p_top, _, ba_p, _, m_p, hm_p_mix, hm_p_reach, hgm_p,
          y_p, hy_p_in, hy_p_ne, um_p, hum_p_y, _, _, z_p, hz_pW, hum_pz, hz_peq, hqstar_side, hformU_p, hformZ_p⟩
      · have := Finset.card_pos.mpr ⟨a, haCL⟩; omega
      have hzp_eq : z_p = qstar := by
        rcases hz_peq with h1 | h2
        · exact absurd (h1 ▸ hz_pW) (hP_notW p1 hp1P hp1_ne)
        · exact h2
      subst z_p
      obtain ⟨_, _, htri_q⟩ := ustar_edge_structure G C h4 hE hL hT g hg pstar q1
        (hp_adj_Q q1 hq1Q) hq1U
      rcases htri_q with ⟨a, haCL, _⟩ | ⟨a_q, ha_q_top, _, ba_q, _, m_q, hm_q_mix, hm_q_reach, hgm_q,
          y_q, hy_q_in, hy_q_ne, um_q, hum_q_y, _, _, z_q, hz_qW, hum_qz, hz_qeq, _, hformU_q, hformZ_q⟩
      · have := Finset.card_pos.mpr ⟨a, haCL⟩; omega
      have hzq_eq : z_q = pstar := by
        rcases hz_qeq with h1 | h2
        · exact h1
        · exact absurd (h2 ▸ hz_qW) (hQ_notW q1 hq1Q hq1_ne)
      subst z_q
      have hmq_ne_mp : m_q ≠ m_p := by
        intro heq; subst heq
        have hm_lt : m_q < C.gates.length := by
          simp only [mixing, orN, gatesWhere, Finset.mem_filter, Finset.mem_range] at hm_q_mix; exact hm_q_mix.1.1
        have hy_eq : y_q = y_p := by
          obtain ⟨_, i0, i1, hin, _, _⟩ := hA m_q hm_lt
          rw [hin] at hgm_q hy_q_in hy_p_in
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hgm_q hy_q_in hy_p_in
          rcases hgm_q with rfl | rfl <;> rcases hy_q_in with rfl | rfl <;> rcases hy_p_in with rfl | rfl <;>
            first | rfl | exact absurd rfl hy_q_ne | exact absurd rfl hy_p_ne
        subst hy_eq
        have humq_side_ap : um_q ∈ side (n := n) C a_p ba_p :=
          ((thm_1506 n G C h4 hE hL hT g hg m_q hm_q_mix hgm_q y_q hy_q_in hy_q_ne).2
            um_q hum_q_y a_p ha_p_top ba_p hm_p_reach).1
        simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha_p_top
        have hW0 := orR_mono n C hA (pairInput um_q qstar) (opnd C a_p ba_p) um_q.val
          ((mem_orIn n C hA _ (by have := opnd_lt' hA a_p ha_p_top.1 ba_p; omega) um_q).mp humq_side_ap)
          (by rw [M1528.P2.W_input n C _ um_q.val um_q.isLt]; simp [pairInput])
        have hW1 := orR_mono n C hA (pairInput um_q qstar) (opnd C a_p (1 - ba_p)) qstar.val
          ((mem_orIn n C hA _ (by have := opnd_lt' hA a_p ha_p_top.1 (1 - ba_p); omega) qstar).mp hqstar_side)
          (by rw [M1528.P2.W_input n C _ qstar.val qstar.isLt]; simp [pairInput])
        have hWa : W n C (pairInput um_q qstar) (n + a_p) = true := by
          rw [W_and n C _ a_p ha_p_top.1 ha_p_top.2.1 (opnd C a_p 0) (opnd C a_p 1) (opnd_eq n C hA a_p ha_p_top.1)
            (opnd_lt' hA a_p ha_p_top.1 0) (opnd_lt' hA a_p ha_p_top.1 1), Bool.and_eq_true]
          fin_cases ba_p <;> [exact ⟨hW0, hW1⟩; exact ⟨hW1, hW0⟩]
        have humq_adj_qstar : G.Adj um_q qstar := by
          have hF := ha_p_top.2.2 (pairInput um_q qstar) hWa; rwa [graphFun_pair] at hF
        exact htri pstar qstar um_q hpq_adj humq_adj_qstar.symm hum_qz
      have hmix2 : 2 ≤ (mixing G C).card := by
        have hsub : ({m_p, m_q} : Finset ℕ) ⊆ mixing G C := by
          intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption
        have hcard := Finset.card_le_card hsub
        rwa [Finset.card_pair hmq_ne_mp.symm] at hcard
      omega
    omega
  ·
    have hU_eq : Ustar G C = EP ∪ EQ := by
      ext e
      simp only [Finset.mem_union, EP, EQ, Finset.mem_image]
      constructor
      · intro he
        rcases hU_class e he with rfl | ⟨p, hp, rfl⟩ | ⟨q, hq, rfl⟩
        · exact absurd he hspqU
        · exact Or.inl ⟨p, hp, rfl⟩
        · exact Or.inr ⟨q, hq, rfl⟩
      · rintro (⟨p, hp, rfl⟩ | ⟨q, hq, rfl⟩)
        · exact (Finset.mem_filter.mp hp).2.2
        · exact (Finset.mem_filter.mp hq).2.2
    have hU_card : (Ustar G C).card = PU'.card + QU'.card := by
      rw [hU_eq, Finset.card_union_of_disjoint hEP_EQ_disj, hEP_card, hEQ_card]
    omega

lemma cover_no_singletons {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g : ℕ) (K : Finset (Fin n))
    (hKcov : ∀ e ∈ starEdges G C, ∃ v ∈ K, v ∈ e)
    (h1528 : G.edgeFinset.card + K.card + (pen G C g K).card + 1 +
      (mixing G C).card + 2 * (centreless G C).card + (coneGates G C g).card ≤
      C.size + (Ustar G C).card + 1)
    (h4 : NoFourCycle G) (hE : G.edgeFinset.Nonempty)
    (hL : IsLeastAO G C) (hT : TopForm G C) (hg : junk G C = {g})
    (hUne : (Ustar G C).Nonempty)
    (hdisj : side (n := n) C g 0 ∩ side (n := n) C g 1 = ∅)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
 :
    ∃ T : Finset (Fin n), (∀ e ∈ G.edgeFinset, ∃ v ∈ T, v ∈ e) ∧
      G.edgeFinset.card + T.card ≤ C.size + 1 := by
  classical
  have hsing (b : Fin 2) (z : Fin n) (hs : side (n := n) C g b = {z}) :
      ∀ e ∈ Ustar G C, z ∈ e := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
      have huv : G.Adj u v := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp he).1
      obtain ⟨hgtrue, _, _⟩ := ustar_edge_structure G C h4 hE hL hT g hg u v huv he
      obtain ⟨h0, h1⟩ := g_pair_sides G C hL hT g hg u v hgtrue
      have hb : u ∈ side (n := n) C g b ∨ v ∈ side (n := n) C g b := by
        fin_cases b
        · exact h0
        · exact h1
      rw [hs] at hb
      simp only [Finset.mem_singleton] at hb
      rcases hb with rfl | rfl
      · exact Sym2.mem_mk_left _ _
      · exact Sym2.mem_mk_right _ _
  obtain ⟨hPne, hQne, _, hW_iff, _, _, _, _, _⟩ := g_semantics G C hL hT g hg
  by_cases hP1 : (side (n := n) C g 0).card ≤ 1
  · obtain ⟨p0, hp0⟩ := Finset.card_eq_one.mp (le_antisymm hP1 (Finset.card_pos.mpr hPne))
    exact one_center G C g K hKcov h1528 h4 hE hL hT hg hUne hdisj 0 p0
      (by rw [hp0]; simp) (hsing 0 p0 hp0)
  by_cases hQ1 : (side (n := n) C g 1).card ≤ 1
  · obtain ⟨q0, hq0⟩ := Finset.card_eq_one.mp (le_antisymm hQ1 (Finset.card_pos.mpr hQne))
    exact one_center G C g K hKcov h1528 h4 hE hL hT hg hUne hdisj 1 q0
      (by rw [hq0]; simp) (hsing 1 q0 hq0)
  have hP2 : 2 ≤ (side (n := n) C g 0).card := by omega
  have hQ2 : 2 ≤ (side (n := n) C g 1).card := by omega
  have h1530 := thm_1530 n G h4 (side (n := n) C g 0) (side (n := n) C g 1) (wmax G C g) hW_iff
  have hU_in_WPQ : ∀ e ∈ Ustar G C, ∃ z ∈ (wmax G C g ∩ side (n := n) C g 0) ∪
      (wmax G C g ∩ side (n := n) C g 1), z ∈ e := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
      have huv : G.Adj u v := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp he).1
      obtain ⟨hgtrue, huvW, _⟩ := ustar_edge_structure G C h4 hE hL hT g hg u v huv he
      obtain ⟨h0, h1⟩ := g_pair_sides G C hL hT g hg u v hgtrue
      rcases huvW with huW | hvW
      · rcases h0 with hu0 | hv0
        · exact ⟨u, Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨huW, hu0⟩), Sym2.mem_mk_left _ _⟩
        · rcases h1 with hu1 | hv1
          · exact ⟨u, Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨huW, hu1⟩), Sym2.mem_mk_left _ _⟩
          · exfalso; have : v ∈ side (n := n) C g 0 ∩ side (n := n) C g 1 := Finset.mem_inter.mpr ⟨hv0, hv1⟩
            rw [hdisj] at this; exact Finset.notMem_empty _ this
      · rcases h0 with hu0 | hv0
        · rcases h1 with hu1 | hv1
          · exfalso; have : u ∈ side (n := n) C g 0 ∩ side (n := n) C g 1 := Finset.mem_inter.mpr ⟨hu0, hu1⟩
            rw [hdisj] at this; exact Finset.notMem_empty _ this
          · exact ⟨v, Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hvW, hv1⟩), Sym2.mem_mk_right _ _⟩
        · exact ⟨v, Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hvW, hv0⟩), Sym2.mem_mk_right _ _⟩
  by_cases hWP : (wmax G C g ∩ side (n := n) C g 0).Nonempty
  · obtain ⟨pstar, hpstar⟩ := Finset.card_eq_one.mp (le_antisymm (h1530.1 hQ2) (Finset.card_pos.mpr hWP))
    have hpW : pstar ∈ wmax G C g := (Finset.mem_inter.mp (by rw [hpstar]; simp)).1
    have hpP : pstar ∈ side (n := n) C g 0 := (Finset.mem_inter.mp (by rw [hpstar]; simp)).2
    by_cases hWQ : (wmax G C g ∩ side (n := n) C g 1).Nonempty
    · obtain ⟨qstar, hqstar⟩ := Finset.card_eq_one.mp (le_antisymm (h1530.2.1 hP2) (Finset.card_pos.mpr hWQ))
      have hqW : qstar ∈ wmax G C g := (Finset.mem_inter.mp (by rw [hqstar]; simp)).1
      have hqQ : qstar ∈ side (n := n) C g 1 := (Finset.mem_inter.mp (by rw [hqstar]; simp)).2
      by_cases hp1 : ∃ p1 ∈ side (n := n) C g 0, p1 ≠ pstar ∧ s(p1, qstar) ∈ Ustar G C
      · by_cases hq1 : ∃ q1 ∈ side (n := n) C g 1, q1 ≠ qstar ∧ s(pstar, q1) ∈ Ustar G C
        · exact two_centers G C g K hKcov h1528 h4 hE hL hT hg hUne
            hdisj htri hP2 hQ2 pstar qstar hpW hpP hqW hqQ hp1 hq1
        ·
          refine one_center G C g K hKcov h1528 h4 hE hL hT hg hUne hdisj 1 qstar hqQ ?_
          intro e he
          obtain ⟨z, hz, hze⟩ := hU_in_WPQ e he
          rw [hpstar, hqstar] at hz
          simp only [Finset.mem_union, Finset.mem_singleton] at hz
          rcases hz with hz | hz
          · subst z
            induction e using Sym2.ind with
            | _ u v =>
              have huv : G.Adj u v := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp he).1
              obtain ⟨hgtrue, _, _⟩ := ustar_edge_structure G C h4 hE hL hT g hg u v huv he
              obtain ⟨_, h1⟩ := g_pair_sides G C hL hT g hg u v hgtrue
              have hp_notQ : pstar ∉ side (n := n) C g 1 := fun h => by
                have : pstar ∈ side (n := n) C g 0 ∩ side (n := n) C g 1 := Finset.mem_inter.mpr ⟨hpP, h⟩
                rw [hdisj] at this; exact Finset.notMem_empty _ this
              rcases Sym2.mem_iff.mp hze with hu | hv
              · subst u
                have hvQ : v ∈ side (n := n) C g 1 := h1.resolve_left hp_notQ
                by_cases hvq : v = qstar
                · subst v; exact Sym2.mem_mk_right _ _
                · exact absurd ⟨v, hvQ, hvq, he⟩ hq1
              · subst v
                have huQ : u ∈ side (n := n) C g 1 := h1.resolve_right hp_notQ
                by_cases huq : u = qstar
                · subst u; exact Sym2.mem_mk_left _ _
                · exact absurd ⟨u, huQ, huq, by rw [Sym2.eq_swap]; exact he⟩ hq1
          · subst z; exact hze
      ·
        refine one_center G C g K hKcov h1528 h4 hE hL hT hg hUne hdisj 0 pstar hpP ?_
        intro e he
        obtain ⟨z, hz, hze⟩ := hU_in_WPQ e he
        rw [hpstar, hqstar] at hz
        simp only [Finset.mem_union, Finset.mem_singleton] at hz
        rcases hz with hz | hz
        · subst z; exact hze
        · subst z
          induction e using Sym2.ind with
          | _ u v =>
            have huv : G.Adj u v := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp he).1
            obtain ⟨hgtrue, _, _⟩ := ustar_edge_structure G C h4 hE hL hT g hg u v huv he
            obtain ⟨h0, _⟩ := g_pair_sides G C hL hT g hg u v hgtrue
            have hq_notP : qstar ∉ side (n := n) C g 0 := fun h => by
              have : qstar ∈ side (n := n) C g 0 ∩ side (n := n) C g 1 := Finset.mem_inter.mpr ⟨h, hqQ⟩
              rw [hdisj] at this; exact Finset.notMem_empty _ this
            rcases Sym2.mem_iff.mp hze with hu | hv
            · subst u
              have hvP : v ∈ side (n := n) C g 0 := h0.resolve_left hq_notP
              by_cases hvp : v = pstar
              · subst v; exact Sym2.mem_mk_right _ _
              · exact absurd ⟨v, hvP, hvp, by rw [Sym2.eq_swap]; exact he⟩ hp1
            · subst v
              have huP : u ∈ side (n := n) C g 0 := h0.resolve_right hq_notP
              by_cases hup : u = pstar
              · subst u; exact Sym2.mem_mk_left _ _
              · exact absurd ⟨u, huP, hup, he⟩ hp1
    ·
      rw [Finset.not_nonempty_iff_eq_empty] at hWQ
      refine one_center G C g K hKcov h1528 h4 hE hL hT hg hUne hdisj 0 pstar hpP ?_
      intro e he
      obtain ⟨z, hz, hze⟩ := hU_in_WPQ e he
      rw [hpstar, hWQ] at hz
      simp only [Finset.union_empty, Finset.mem_singleton] at hz
      rwa [← hz]
  ·
    rw [Finset.not_nonempty_iff_eq_empty] at hWP
    have hWQ : (wmax G C g ∩ side (n := n) C g 1).Nonempty := by
      obtain ⟨e, he⟩ := hUne
      obtain ⟨z, hz, _⟩ := hU_in_WPQ e he
      rw [hWP, Finset.empty_union] at hz
      exact ⟨z, hz⟩
    obtain ⟨qstar, hqstar⟩ := Finset.card_eq_one.mp (le_antisymm (h1530.2.1 hP2) (Finset.card_pos.mpr hWQ))
    have hqW : qstar ∈ wmax G C g := (Finset.mem_inter.mp (by rw [hqstar]; simp)).1
    have hqQ : qstar ∈ side (n := n) C g 1 := (Finset.mem_inter.mp (by rw [hqstar]; simp)).2
    refine one_center G C g K hKcov h1528 h4 hE hL hT hg hUne hdisj 1 qstar hqQ ?_
    intro e he
    obtain ⟨z, hz, hze⟩ := hU_in_WPQ e he
    rw [hWP, hqstar] at hz
    simp only [Finset.empty_union, Finset.mem_singleton] at hz
    rwa [← hz]

lemma one_junk_cover {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g : ℕ) (h4 : NoFourCycle G)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hL : IsLeastAO G C) (hT : TopForm G C) (hg : junk G C = {g})
    (hsil : ∀ u : Fin n, gateVal n C g (pairInput u u) = false) :
    ∃ T : Finset (Fin n), (∀ e ∈ G.edgeFinset, ∃ v ∈ T, v ∈ e) ∧
      G.edgeFinset.card + T.card ≤ C.size + 1 := by
  classical
  by_cases hE : G.edgeFinset.Nonempty
  · obtain ⟨K, hKcov, _, _, h1528⟩ := thm_1528 n G C h4 hE hL hT g hg
    by_cases hUne : (Ustar G C).Nonempty
    · have hdisj : side (n := n) C g 0 ∩ side (n := n) C g 1 = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro u hu
        obtain ⟨hu0, hu1⟩ := Finset.mem_inter.mp hu
        have hf := ((g_semantics G C hL hT g hg).2.2.1 (pairInput u u)).mpr
          ⟨⟨u, hu0, by simp [pairInput]⟩, ⟨u, hu1, by simp [pairInput]⟩⟩
        rw [W_eq_gateVal, hsil u] at hf
        contradiction
      exact cover_no_singletons G C g K hKcov h1528 h4 hE hL hT hg hUne hdisj htri
    · have hU0 : Ustar G C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hUne
      refine ⟨K, ?_, ?_⟩
      · intro e he
        apply hKcov e
        by_contra hs
        have hu : e ∈ Ustar G C := Finset.mem_sdiff.mpr ⟨he, hs⟩
        rw [hU0] at hu
        exact Finset.notMem_empty _ hu
      · rw [hU0, Finset.card_empty] at h1528
        omega
  · have hE0 : G.edgeFinset = ∅ := Finset.not_nonempty_iff_eq_empty.mp hE
    refine ⟨∅, ?_, ?_⟩
    · intro e he
      rw [hE0] at he
      exact (Finset.notMem_empty _ he).elim
    · rw [hE0]
      simp

lemma cover_inter_ge_two {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (hE : G.edgeFinset.Nonempty)
    (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g})
    (K : Finset (Fin n))
    (hKcov : ∀ e ∈ starEdges G C, ∃ v ∈ K, v ∈ e)
    (h1528 : G.edgeFinset.card + K.card + (pen G C g K).card + 1 +
      (mixing G C).card + 2 * (centreless G C).card + (coneGates G C g).card ≤
      C.size + (Ustar G C).card + 1)
    (hUne : (Ustar G C).Nonempty)
    (hI2 : 2 ≤ (side (n := n) C g 0 ∩ side (n := n) C g 1).card) :
    ∃ T : Finset (Fin n), (∀ e ∈ G.edgeFinset, ∃ v ∈ T, v ∈ e) ∧
      G.edgeFinset.card + T.card ≤ C.size + 1 := by
  classical
  have hA : AO n C := AO_of_IsAO2 n C hL.1
  have hg_lt := (junk_single_props G C hL hT g hg).1
  obtain ⟨_, _, hgeval, hW_iff, _, _, _, _, _⟩ := g_semantics G C hL hT g hg
  have h1529 := thm_1529 n G h4 (side (n := n) C g 0) (side (n := n) C g 1) (wmax G C g) hW_iff
  have h1530 := thm_1530 n G h4 (side (n := n) C g 0) (side (n := n) C g 1) (wmax G C g) hW_iff
  have hWle1 : (wmax G C g).card ≤ 1 := h1529.2.2.2.2 hI2
  have hWne : (wmax G C g).Nonempty := by
    obtain ⟨e, he⟩ := hUne
    induction e using Sym2.ind with
    | _ u v =>
      have huv : G.Adj u v := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp he).1
      obtain ⟨_, huvW, _⟩ := ustar_edge_structure G C h4 hE hL hT g hg u v huv he
      rcases huvW with hu | hv <;> [exact ⟨u, hu⟩; exact ⟨v, hv⟩]
  obtain ⟨w0, hw0_eq⟩ := Finset.card_eq_one.mp (le_antisymm hWle1 (Finset.card_pos.mpr hWne))
  have hw0W : w0 ∈ wmax G C g := by rw [hw0_eq]; simp
  obtain ⟨h0_lt, h0_no⟩ := no_and_in_g_opnd G C hL hT g hg 0
  obtain ⟨h1_lt, h1_no⟩ := no_and_in_g_opnd G C hL hT g hg 1
  by_cases hQall : ∀ q ∈ side (n := n) C g 1, G.Adj w0 q
  · exfalso
    refine replace_gate_by_wire G C hE hL hT g hg (opnd C g 1) h1_lt ?_ (Or.inr ⟨w0, hw0_eq, ?_⟩)
    · intro u v huv hU
      obtain ⟨hgtrue, _, _⟩ := ustar_edge_structure G C h4 hE hL hT g hg u v huv hU
      rw [← W_eq_gateVal, hgeval] at hgtrue
      exact (pure_or_wire_eval C hA (opnd C g 1) (by omega) h1_no).2 (pairInput u v) |>.mpr hgtrue.2
    · intro x hxw0 hW1
      obtain ⟨q, hqQ, hxq⟩ := (pure_or_wire_eval C hA (opnd C g 1) (by omega) h1_no).2 x |>.mp hW1
      simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
        Bool.false_or, decide_eq_true_eq]
      exact ⟨w0, q, hQall q hqQ, hxw0, hxq⟩
  by_cases hPall : ∀ p ∈ side (n := n) C g 0, G.Adj w0 p
  · exfalso
    refine replace_gate_by_wire G C hE hL hT g hg (opnd C g 0) h0_lt ?_ (Or.inr ⟨w0, hw0_eq, ?_⟩)
    · intro u v huv hU
      obtain ⟨hgtrue, _, _⟩ := ustar_edge_structure G C h4 hE hL hT g hg u v huv hU
      rw [← W_eq_gateVal, hgeval] at hgtrue
      exact (pure_or_wire_eval C hA (opnd C g 0) (by omega) h0_no).2 (pairInput u v) |>.mpr hgtrue.1
    · intro x hxw0 hW0
      obtain ⟨p, hpP, hxp⟩ := (pure_or_wire_eval C hA (opnd C g 0) (by omega) h0_no).2 x |>.mp hW0
      simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
        Bool.false_or, decide_eq_true_eq]
      exact ⟨w0, p, hPall p hpP, hxw0, hxp⟩
  have hw0_notP : w0 ∉ side (n := n) C g 0 := fun h => hQall (h1529.1 w0 hw0W h).2
  have hw0_notQ : w0 ∉ side (n := n) C g 1 := fun h => hPall (h1529.2.1 w0 hw0W h).2
  push Not at hQall hPall
  obtain ⟨q', hq'Q, hq'nadj⟩ := hQall
  obtain ⟨p', hp'P, hp'nadj⟩ := hPall
  have hp'q' : G.Adj p' q' := by
    rcases (hW_iff w0).mp hw0W p' hp'P q' hq'Q with h | h | h
    · exact h
    · exact absurd h.symm hp'nadj
    · exact absurd h.symm hq'nadj
  let IU := (side (n := n) C g 0 ∩ side (n := n) C g 1).filter fun b => s(w0, b) ∈ Ustar G C
  have hU_eq : Ustar G C = IU.image (fun b => s(w0, b)) := by
    ext e
    induction e using Sym2.ind with
    | _ u v =>
      simp only [Finset.mem_image, IU, Finset.mem_filter]
      constructor
      · intro hU
        have huv : G.Adj u v := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp hU).1
        obtain ⟨hgtrue, huvW, _⟩ := ustar_edge_structure G C h4 hE hL hT g hg u v huv hU
        obtain ⟨h0, h1⟩ := g_pair_sides G C hL hT g hg u v hgtrue
        rcases huvW with huW | hvW
        · have hu0 : u = w0 := by rw [hw0_eq, Finset.mem_singleton] at huW; exact huW
          subst u
          have hvI := (h1530.2.2.1 w0 v huv h0 h1 hw0W).2.2 hw0_notP hw0_notQ
          exact ⟨v, ⟨hvI, hU⟩, rfl⟩
        · have hv0 : v = w0 := by rw [hw0_eq, Finset.mem_singleton] at hvW; exact hvW
          subst v
          have huI := (h1530.2.2.1 w0 u huv.symm h0.symm h1.symm hw0W).2.2 hw0_notP hw0_notQ
          exact ⟨u, ⟨huI, by rw [Sym2.eq_swap]; exact hU⟩, Sym2.eq_swap⟩
      · rintro ⟨b, ⟨_, hU⟩, heq⟩; rwa [← heq]
  have hIU_adj : ∀ b ∈ IU, G.Adj w0 b := fun b hb =>
    SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp hb).2).1
  have hIU_notStar : ∀ b ∈ IU, s(w0, b) ∉ starEdges G C := fun b hb =>
    (Finset.mem_sdiff.mp (Finset.mem_filter.mp hb).2).2
  have hU_card : (Ustar G C).card = IU.card := by
    rw [hU_eq, Finset.card_image_of_injOn]
    intro b1 hb1 b2 hb2 heq
    have hadj := hIU_adj b1 hb1
    rcases Sym2.eq_iff.mp heq with ⟨_, h⟩ | ⟨_, h⟩
    · exact h
    · exact absurd h.symm hadj.ne
  have hlamIU : ∀ h ∈ lam G C, ((orIn n C (n + h)) ∩ IU).card ≤ 1 :=
    lam_card_le_one_of_common_nbr G h4 C hL w0 IU hIU_adj
      (fun a _ ha _ _ => Or.inl (hIU_notStar a ha))
  have hIU_sub : IU ⊆ side (n := n) C g 0 := by
    intro x hx
    exact (Finset.mem_inter.mp (Finset.mem_filter.mp hx).1).1
  have hcg := g_cone_gate_count G C hL hT g hg 0 IU hIU_sub hlamIU
  have hcg_le : ((coneGates G C g).filter fun h => OrR n C (opnd C g 0) (n + h)).card ≤
      (coneGates G C g).card := Finset.card_le_card (Finset.filter_subset _ _)
  have hXcov : ∀ e ∈ Ustar G C, ∃ v ∈ K ∪ {w0}, v ∈ e := by
    intro e he
    rw [hU_eq, Finset.mem_image] at he
    obtain ⟨b, _, rfl⟩ := he
    exact ⟨w0, Finset.mem_union_right _ (Finset.mem_singleton_self _), Sym2.mem_mk_left _ _⟩
  have hmixcl := ustar_ne_implies_mix_or_cl G C h4 hE hL hT g hg hUne
  have hxcard : (({w0} : Finset (Fin n)) \ K).card ≤ 1 :=
    (Finset.card_le_card Finset.sdiff_subset).trans (by simp)
  apply cover_of_budget G C g K hKcov h1528 {w0} hXcov
  omega

lemma cover_inter_one_side {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (h4 : NoFourCycle G) (hE : G.edgeFinset.Nonempty)
    (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g})
    (K : Finset (Fin n))
    (hKcov : ∀ e ∈ starEdges G C, ∃ v ∈ K, v ∈ e)
    (hformU : formU G C g ⊆ K) (hformZ : formZ G C g ⊆ K)
    (h1528 : G.edgeFinset.card + K.card + (pen G C g K).card + 1 +
      (mixing G C).card + 2 * (centreless G C).card + (coneGates G C g).card ≤
      C.size + (Ustar G C).card + 1)
    (v : Fin n) (hInter : side (n := n) C g 0 ∩ side (n := n) C g 1 = {v})
    (b : Fin 2) (wP : Fin n)
    (hWb : wmax G C g ∩ side (n := n) C g b = {wP})
    (hW1b : wmax G C g ∩ side (n := n) C g (1 - b) = ∅) :
    ∃ T : Finset (Fin n), (∀ e ∈ G.edgeFinset, ∃ v ∈ T, v ∈ e) ∧
      G.edgeFinset.card + T.card ≤ C.size + 1 := by
  classical
  have hA : AO n C := AO_of_IsAO2 n C hL.1
  have hg_lt := (junk_single_props G C hL hT g hg).1
  obtain ⟨_, _, hgeval, hW_iff, _, _, _, _, _⟩ := g_semantics G C hL hT g hg
  have h1529 := thm_1529 n G h4 (side (n := n) C g 0) (side (n := n) C g 1) (wmax G C g) hW_iff
  have h1530 := thm_1530 n G h4 (side (n := n) C g 0) (side (n := n) C g 1) (wmax G C g) hW_iff
  have hv_mem_inter : v ∈ side (n := n) C g 0 ∩ side (n := n) C g 1 := by rw [hInter]; simp
  have hv0 : v ∈ side (n := n) C g 0 := (Finset.mem_inter.mp hv_mem_inter).1
  have hv1 : v ∈ side (n := n) C g 1 := (Finset.mem_inter.mp hv_mem_inter).2
  have hv_b : v ∈ side (n := n) C g b := by rcases fin2_cases b with rfl | rfl <;> assumption
  have hv_1b : v ∈ side (n := n) C g (1 - b) := by rcases fin2_cases b with rfl | rfl <;> assumption
  have hv_notW : v ∉ wmax G C g := h1529.2.2.2.1 v hv_mem_inter
  have hv_adj_W : ∀ w ∈ wmax G C g, G.Adj v w := h1529.2.2.1 v hv_mem_inter
  have hwP_W : wP ∈ wmax G C g := (Finset.mem_inter.mp (by rw [hWb]; simp)).1
  have hwP_b : wP ∈ side (n := n) C g b := (Finset.mem_inter.mp (by rw [hWb]; simp)).2
  have hwP_not1b : wP ∉ side (n := n) C g (1 - b) := by
    intro hmem
    have : wP ∈ wmax G C g ∩ side (n := n) C g (1 - b) := Finset.mem_inter.mpr ⟨hwP_W, hmem⟩
    rw [hW1b] at this; exact Finset.notMem_empty _ this
  have hwP_adj_1b : ∀ q ∈ side (n := n) C g (1 - b), G.Adj wP q := by
    rcases fin2_cases b with rfl | rfl
    · exact (h1529.1 wP hwP_W hwP_b).2
    · exact (h1529.2.1 wP hwP_W hwP_b).2
  have hvwP_adj : G.Adj v wP := hv_adj_W wP hwP_W
  have hW_clause4 : ∀ u : Fin n, u ≠ v → ((Finset.univ.filter fun w => G.Adj u w) ∩ wmax G C g).card ≤ 1 :=
    h1530.2.2.2 v hInter
  let QU := (side (n := n) C g (1 - b)).filter fun q => q ≠ v ∧ s(wP, q) ∈ Ustar G C
  let WU := (wmax G C g).filter fun w => s(w, v) ∈ Ustar G C
  let EQ := QU.image (fun q => s(wP, q))
  let EW := WU.image (fun w => s(w, v))
  have hU_eq : Ustar G C = EQ ∪ EW := by
    ext e
    induction e using Sym2.ind with
    | _ x y =>
      simp only [Finset.mem_union, EQ, EW, Finset.mem_image, QU, WU, Finset.mem_filter]
      constructor
      · intro hU
        have hxy : G.Adj x y := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp hU).1
        obtain ⟨hgtrue, hxyW, _⟩ := ustar_edge_structure G C h4 hE hL hT g hg x y hxy hU
        obtain ⟨h0, h1⟩ := g_pair_sides G C hL hT g hg x y hgtrue
        have hclassify : ∀ a c : Fin n, G.Adj a c → (a ∈ side (n := n) C g 0 ∨ c ∈ side (n := n) C g 0) →
            (a ∈ side (n := n) C g 1 ∨ c ∈ side (n := n) C g 1) → a ∈ wmax G C g →
            s(a, c) ∈ Ustar G C →
            (∃ q, (q ∈ side (n := n) C g (1 - b) ∧ q ≠ v ∧ s(wP, q) ∈ Ustar G C) ∧ s(wP, q) = s(a, c)) ∨
            (∃ w, (w ∈ wmax G C g ∧ s(w, v) ∈ Ustar G C) ∧ s(w, v) = s(a, c)) := by
          intro a c hac h0' h1' haW haU
          have hc3 := h1530.2.2.1 a c hac h0' h1' haW
          by_cases hab : a ∈ side (n := n) C g b
          · have haw : a = wP := by
              have : a ∈ wmax G C g ∩ side (n := n) C g b := Finset.mem_inter.mpr ⟨haW, hab⟩
              rwa [hWb, Finset.mem_singleton] at this
            subst a
            have hc1b : c ∈ side (n := n) C g (1 - b) := by
              rcases fin2_cases b with rfl | rfl
              · exact hc3.1 hab
              · exact hc3.2.1 hab
            by_cases hcv : c = v
            · subst c; exact Or.inr ⟨wP, ⟨haW, haU⟩, rfl⟩
            · exact Or.inl ⟨c, ⟨hc1b, hcv, haU⟩, rfl⟩
          · have ha1b : a ∉ side (n := n) C g (1 - b) := fun h => by
              have : a ∈ wmax G C g ∩ side (n := n) C g (1 - b) := Finset.mem_inter.mpr ⟨haW, h⟩
              rw [hW1b] at this; exact Finset.notMem_empty _ this
            have hcI : c ∈ side (n := n) C g 0 ∩ side (n := n) C g 1 := by
              rcases fin2_cases b with rfl | rfl
              · exact hc3.2.2 hab ha1b
              · exact hc3.2.2 ha1b hab
            rw [hInter, Finset.mem_singleton] at hcI
            subst c
            exact Or.inr ⟨a, ⟨haW, haU⟩, rfl⟩
        rcases hxyW with hxW | hyW
        · exact hclassify x y hxy h0 h1 hxW hU
        · rcases hclassify y x hxy.symm h0.symm h1.symm hyW (by rw [Sym2.eq_swap]; exact hU) with
            ⟨q, hq, heq⟩ | ⟨w, hw, heq⟩
          · exact Or.inl ⟨q, hq, heq.trans Sym2.eq_swap⟩
          · exact Or.inr ⟨w, hw, heq.trans Sym2.eq_swap⟩
      · rintro (⟨q, ⟨_, _, hU⟩, heq⟩ | ⟨w, ⟨_, hU⟩, heq⟩) <;> rwa [← heq]
  have hEQ_EW_disj : Disjoint EQ EW := by
    rw [Finset.disjoint_left]
    intro e h1 h2
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp h1
    obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp h2
    have hq_nev := (Finset.mem_filter.mp hq).2.1
    rcases Sym2.eq_iff.mp heq with ⟨_, hqv⟩ | ⟨_, hwv⟩
    · exact hq_nev hqv.symm
    · exact hvwP_adj.ne hwv
  have hEQ_card : EQ.card = QU.card := by
    rw [Finset.card_image_of_injOn]
    intro q1 hq1 q2 hq2 heq
    have hadj := hwP_adj_1b q1 (Finset.mem_filter.mp hq1).1
    rcases Sym2.eq_iff.mp heq with ⟨_, h⟩ | ⟨_, h⟩
    · exact h
    · exact absurd h.symm hadj.ne
  have hEW_card : EW.card = WU.card := by
    rw [Finset.card_image_of_injOn]
    intro w1 hw1 w2 hw2 heq
    have hadj := hv_adj_W w1 (Finset.mem_filter.mp hw1).1
    rcases Sym2.eq_iff.mp heq with ⟨h, _⟩ | ⟨h, _⟩
    · exact h
    · exact absurd h hadj.ne'
  have hU_card : (Ustar G C).card = QU.card + WU.card := by
    rw [hU_eq, Finset.card_union_of_disjoint hEQ_EW_disj, hEQ_card, hEW_card]
  by_cases hQUempty : QU = ∅
  · exfalso
    refine replace_gate_by_wire G C hE hL hT g hg v.val (by have := v.isLt; omega) ?_ (Or.inl ?_)
    · intro x y _ hU
      rw [hU_eq, show EQ = ∅ by simp [EQ, hQUempty], Finset.empty_union, Finset.mem_image] at hU
      obtain ⟨w, _, heq⟩ := hU
      rw [W_input n C _ v.val v.isLt, pairInput_true]
      rcases Sym2.eq_iff.mp heq with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact Or.inr rfl
      · exact Or.inl rfl
    · intro x hxv
      rw [W_input n C x v.val v.isLt] at hxv
      rw [hgeval]
      exact ⟨⟨v, hv0, hxv⟩, ⟨v, hv1, hxv⟩⟩
  have hQU_ne : QU.Nonempty := Finset.nonempty_iff_ne_empty.mpr hQUempty
  let Cg1b := (coneGates G C g).filter fun h => OrR n C (opnd C g (1 - b)) (n + h)
  have hCg1b_lb : QU.card ≤ Cg1b.card := by
    let T := insert v QU
    have hv_notQU : v ∉ QU := fun h => (Finset.mem_filter.mp h).2.1 rfl
    have hT_sub : T ⊆ side (n := n) C g (1 - b) := by
      intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hq'
      · exact hv_1b
      · exact (Finset.mem_filter.mp hq').1
    have hlamT : ∀ h ∈ lam G C, ((orIn n C (n + h)) ∩ T).card ≤ 1 := by
      refine lam_card_le_one_of_common_nbr G h4 C hL wP T (fun q hq => hwP_adj_1b q (hT_sub hq)) ?_
      intro x y hx hy hxy
      rcases Finset.mem_insert.mp hx with rfl | hx'
      · rcases Finset.mem_insert.mp hy with rfl | hy'
        · exact absurd rfl hxy
        · exact Or.inr (Finset.mem_sdiff.mp (Finset.mem_filter.mp hy').2.2).2
      · exact Or.inl (Finset.mem_sdiff.mp (Finset.mem_filter.mp hx').2.2).2
    have h : T.card ≤ 1 + Cg1b.card := g_cone_gate_count G C hL hT g hg (1 - b) T hT_sub hlamT
    rw [Finset.card_insert_of_notMem hv_notQU] at h
    omega
  obtain ⟨hb_lt, hb_noAnd⟩ := no_and_in_g_opnd G C hL hT g hg b
  have hroot_b : ∃ hb, opnd C g b = n + hb ∧ hb < C.gates.length ∧ (gateAt C hb).op = GateOp.or := by
    by_cases hwn : opnd C g b < n
    · exfalso
      have hv_eq : v.val = opnd C g b := by
        have hr := (mem_orIn n C hA _ (by omega) v).mp hv_b
        rcases Relation.ReflTransGen.cases_head hr with heq | ⟨_, ⟨k, hk, _⟩, _⟩
        · exact heq.symm
        · omega
      have hw_eq : wP.val = opnd C g b := by
        have hr := (mem_orIn n C hA _ (by omega) wP).mp hwP_b
        rcases Relation.ReflTransGen.cases_head hr with heq | ⟨_, ⟨k, hk, _⟩, _⟩
        · exact heq.symm
        · omega
      exact hvwP_adj.ne (Fin.ext (hv_eq.trans hw_eq.symm))
    · refine ⟨opnd C g b - n, by omega, by omega, ?_⟩
      rcases (hA (opnd C g b - n) (by omega)).1 with hop | hop
      · exact absurd (show OrR n C (opnd C g b) (n + (opnd C g b - n)) by
          rw [show n + (opnd C g b - n) = opnd C g b by omega]; exact Relation.ReflTransGen.refl)
          (hb_noAnd _ (by omega) hop)
      · exact hop
  obtain ⟨hb, hhb_eq, hhb_lt, hhb_op⟩ := hroot_b
  have hhb_notLam : hb ∉ lam G C := by
    intro hlam
    obtain ⟨c, hc⟩ := lam_has_center G C hL hb hlam
    have hcv := (hc v (by
      change v ∈ orIn n C (opnd C g b) at hv_b
      rwa [hhb_eq] at hv_b)).1
    have hcw := (hc wP (by
      change wP ∈ orIn n C (opnd C g b) at hwP_b
      rwa [hhb_eq] at hwP_b)).1
    exact htri c v wP hcv hvwP_adj hcw.symm
  obtain ⟨hhb_orN, hhb_notMix⟩ := pure_or_gate_in_orN_not_mixing G C hL (opnd C g b) (by omega)
    hb_noAnd hb hhb_lt hhb_op (by rw [hhb_eq]; exact Relation.ReflTransGen.refl)
  have hhb_cg : hb ∈ coneGates G C g := by
    simp only [coneGates, Finset.mem_filter, Finset.mem_sdiff]
    refine ⟨⟨⟨hhb_orN, hhb_notLam⟩, hhb_notMix⟩, ?_⟩
    have hre := orR_orReaches n C hA hb hhb_lt (opnd C g b) (by omega)
      (by rw [hhb_eq]; exact Relation.ReflTransGen.refl)
    rcases fin2_cases b with rfl | rfl
    · exact Or.inl hre
    · exact Or.inr (Or.inl hre)
  have hhb_not_Cg1b : hb ∉ Cg1b := by
    intro hmem
    have hr1b := (Finset.mem_filter.mp hmem).2
    have hwP_orR := (mem_orIn n C hA (n + hb) (by omega) wP).mp
      (by change wP ∈ orIn n C (opnd C g b) at hwP_b; rwa [hhb_eq] at hwP_b)
    have hwP_in1b : wP ∈ side (n := n) C g (1 - b) :=
      (mem_orIn n C hA (opnd C g (1 - b)) (by have := opnd_lt' hA g hg_lt (1 - b); omega) wP).mpr
        (hr1b.trans hwP_orR)
    exact hwP_not1b hwP_in1b
  let Wcl := WU.filter fun w =>
    ∃ a ∈ centreless G C, ∃ ba : Fin 2, opnd C a ba = n + g ∧ w ∈ side (n := n) C a (1 - ba)
  let Wmix := WU \ Wcl
  have hWU_split : Wcl.card + Wmix.card = WU.card := by
    have h1 : Wcl ∪ Wmix = WU := Finset.union_sdiff_of_subset (Finset.filter_subset _ _)
    rw [← h1, Finset.card_union_of_disjoint Finset.disjoint_sdiff]
  let Rcl := (centreless G C).biUnion fun a =>
    (Finset.univ : Finset (Fin 2)).filter (fun ba => opnd C a ba = n + g) |>.image fun ba => opnd C a (1 - ba)
  have hRcl_card : Rcl.card ≤ (centreless G C).card := by
    calc Rcl.card ≤ ∑ a ∈ centreless G C,
          (((Finset.univ : Finset (Fin 2)).filter fun ba => opnd C a ba = n + g).image fun ba => opnd C a (1 - ba)).card :=
            Finset.card_biUnion_le
      _ ≤ ∑ _a ∈ centreless G C, 1 := by
            refine Finset.sum_le_sum fun a ha => ?_
            refine Finset.card_le_one.mpr fun r1 hr1 r2 hr2 => ?_
            obtain ⟨b1, hb1, rfl⟩ := Finset.mem_image.mp hr1
            obtain ⟨b2, hb2, rfl⟩ := Finset.mem_image.mp hr2
            have h1 := (Finset.mem_filter.mp hb1).2
            have h2 := (Finset.mem_filter.mp hb2).2
            have hb_eq : b1 = b2 := by
              by_contra hne
              have h01 : opnd C a 0 = n + g ∧ opnd C a 1 = n + g := by
                rcases fin2_cases b1 with rfl | rfl <;> rcases fin2_cases b2 with rfl | rfl
                · exact absurd rfl hne
                · exact ⟨h1, h2⟩
                · exact ⟨h2, h1⟩
                · exact absurd rfl hne
              have ha_top : a ∈ tops G C := (Finset.mem_filter.mp ha).1
              simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha_top
              exact (junk_single_props G C hL hT g hg).2.2.1 (fun x hx => ha_top.2.2 x (by
                rw [← W_eq_gateVal, W_and n C x a ha_top.1 ha_top.2.1 (opnd C a 0) (opnd C a 1)
                  (opnd_eq n C hA a ha_top.1) (opnd_lt' hA a ha_top.1 0) (opnd_lt' hA a ha_top.1 1),
                  h01.1, h01.2, Bool.and_self]; exact hx))
            rw [hb_eq]
      _ = (centreless G C).card := by simp
  have hRcl_props : ∀ r ∈ Rcl, r < n + C.gates.length ∧
      orIn n C r ⊆ wmax G C g ∧
      (∀ h < C.gates.length, (gateAt C h).op = GateOp.and → ¬ OrR n C r (n + h)) ∧
      ∃ a ∈ centreless G C, ∃ ba : Fin 2, opnd C a ba = n + g ∧ r = opnd C a (1 - ba) := by
    intro r hr
    obtain ⟨a, haCL, hr'⟩ := Finset.mem_biUnion.mp hr
    obtain ⟨ba, hba_f, rfl⟩ := Finset.mem_image.mp hr'
    have hba_g : opnd C a ba = n + g := (Finset.mem_filter.mp hba_f).2
    have ha_top : a ∈ tops G C := (Finset.mem_filter.mp haCL).1
    have ha_lt : a < C.gates.length := by
      simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha_top; exact ha_top.1
    have hlt := opnd_lt' hA a ha_lt (1 - ba)
    obtain ⟨ba0, hba0_g, _, hba0_subW, _⟩ := thm_1503 n G C hE hL hT g hg a haCL
    have hba_eq : ba = ba0 := by
      by_contra hne
      have h01 : opnd C a 0 = n + g ∧ opnd C a 1 = n + g := by
        rcases fin2_cases ba with rfl | rfl <;> rcases fin2_cases ba0 with rfl | rfl
        · exact absurd rfl hne
        · exact ⟨hba_g, hba0_g⟩
        · exact ⟨hba0_g, hba_g⟩
        · exact absurd rfl hne
      simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha_top
      exact (junk_single_props G C hL hT g hg).2.2.1 (fun x hx => ha_top.2.2 x (by
        rw [← W_eq_gateVal, W_and n C x a ha_top.1 ha_top.2.1 (opnd C a 0) (opnd C a 1)
          (opnd_eq n C hA a ha_top.1) (opnd_lt' hA a ha_top.1 0) (opnd_lt' hA a ha_top.1 1),
          h01.1, h01.2, Bool.and_self]; exact hx))
    subst ba
    refine ⟨by omega, hba0_subW, ?_, a, haCL, ba0, hba0_g, rfl⟩
    intro h hh hop hr_and
    have hmem : opnd C a (1 - ba0) ∈ (gateAt C a).inputs := by
      have := opnd_eq n C hA a ha_lt; rcases fin2_cases ba0 with rfl | rfl <;> rw [this] <;> simp
    have hic : InCone n C h a := by
      by_cases h1 : opnd C a (1 - ba0) < n
      · have := orR_le n C hA _ _ hr_and; omega
      · obtain ⟨k, hkeq⟩ : ∃ k, opnd C a (1 - ba0) = n + k := ⟨opnd C a (1 - ba0) - n, by omega⟩
        rcases orR_cone n C hA h (opnd C a (1 - ba0)) hr_and k hkeq (by omega) with rfl | hc
        · exact M1528.P2.inCone_c1 n C hA h a ha_lt (hkeq ▸ hmem)
        · exact M1528.P2.inCone_c2 n C hA h k a ha_lt hc (hkeq ▸ hmem)
    have hhg := (junk_single_props G C hL hT g hg).2.2.2.2.2 a ha_top h hh hop hic
    rw [hhg] at hr_and
    simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha_top
    exact (junk_single_props G C hL hT g hg).2.2.1 (fun x hx => ha_top.2.2 x (by
      have h0 : W n C x (opnd C a ba0) = true := by rw [hba0_g]; exact hx
      have h1 : W n C x (opnd C a (1 - ba0)) = true := orR_mono n C hA x _ _ hr_and hx
      rw [← W_eq_gateVal, W_and n C x a ha_top.1 ha_top.2.1 (opnd C a 0) (opnd C a 1)
        (opnd_eq n C hA a ha_top.1) (opnd_lt' hA a ha_top.1 0) (opnd_lt' hA a ha_top.1 1),
        Bool.and_eq_true]
      rcases fin2_cases ba0 with rfl | rfl <;> [exact ⟨h0, h1⟩; exact ⟨h1, h0⟩]))
  let Cgcl := (coneGates G C g).filter fun h => ∃ r ∈ Rcl, OrR n C r (n + h)
  have hWcl_lb : Wcl.card ≤ (centreless G C).card + Cgcl.card := by
    have hlamWcl : ∀ h ∈ lam G C, ((orIn n C (n + h)) ∩ Wcl).card ≤ 1 := by
      refine lam_card_le_one_of_common_nbr G h4 C hL v Wcl ?_ ?_
      · intro w hw; exact hv_adj_W w (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).1
      · intro x _ hx _ _
        exact Or.inl (by rw [Sym2.eq_swap]; exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2).2)
    have hbound := or_dag_leaf_bound C hA Wcl (lam G C) hlamWcl Rcl
      (fun r hr => (hRcl_props r hr).1) (fun r hr => (hRcl_props r hr).2.2.1)
    have hsubWcl : Wcl ⊆ Rcl.biUnion (fun r => orIn n C r) := by
      intro w hw
      obtain ⟨_, a, haCL, ba, hbag, hw_side⟩ := Finset.mem_filter.mp hw
      refine Finset.mem_biUnion.mpr ⟨opnd C a (1 - ba), ?_, hw_side⟩
      refine Finset.mem_biUnion.mpr ⟨a, haCL, Finset.mem_image.mpr ⟨ba, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbag⟩, rfl⟩⟩
    have hlhs : (Rcl.biUnion (fun r => orIn n C r) ∩ Wcl) = Wcl := Finset.inter_eq_right.mpr hsubWcl
    rw [hlhs] at hbound
    have hF_sub : ((Finset.range C.gates.length).filter fun h =>
        (gateAt C h).op = GateOp.or ∧ h ∉ lam G C ∧ ∃ r ∈ Rcl, OrR n C r (n + h)) ⊆ Cgcl := by
      intro h hh
      obtain ⟨hrng, hop, hnotLam, r, hrR, hrh⟩ := Finset.mem_filter.mp hh
      have hh_lt := Finset.mem_range.mp hrng
      obtain ⟨hr_lt, _, hr_noAnd, a, haCL, ba, hbag, rfl⟩ := hRcl_props r hrR
      obtain ⟨horN, hnotMix⟩ := pure_or_gate_in_orN_not_mixing G C hL _ hr_lt hr_noAnd h hh_lt hop hrh
      refine Finset.mem_filter.mpr ⟨?_, opnd C a (1 - ba), hrR, hrh⟩
      simp only [coneGates, Finset.mem_filter, Finset.mem_sdiff]
      exact ⟨⟨⟨horN, hnotLam⟩, hnotMix⟩, Or.inr (Or.inr ⟨a, haCL, ba, hbag,
        orR_orReaches n C hA h hh_lt _ hr_lt hrh⟩)⟩
    have hF_le := Finset.card_le_card hF_sub
    omega
  have hCgcl_subW : ∀ h ∈ Cgcl, (orIn n C (n + h)).Nonempty ∧ orIn n C (n + h) ⊆ wmax G C g := by
    intro h hh
    obtain ⟨_, r, hrR, hrh⟩ := Finset.mem_filter.mp hh
    obtain ⟨hr_lt, hr_subW, hr_noAnd, _⟩ := hRcl_props r hrR
    have hh_lt : h < C.gates.length := by have := orR_le n C hA _ _ hrh; omega
    have hne := (pure_or_wire_eval C hA (n + h) (by omega)
      (fun k hk hop hrk => hr_noAnd k hk hop (hrh.trans hrk))).1
    refine ⟨hne, fun u hu => hr_subW ?_⟩
    exact (mem_orIn n C hA r hr_lt u).mpr (hrh.trans ((mem_orIn n C hA (n + h) (by omega) u).mp hu))
  have hCgcl_disj_Cg1b : Disjoint Cgcl Cg1b := by
    rw [Finset.disjoint_left]
    intro h h1 h2
    obtain ⟨⟨u, hu⟩, hsubW⟩ := hCgcl_subW h h1
    have hr1b := (Finset.mem_filter.mp h2).2
    have hh_lt : h < C.gates.length := by have := orR_le n C hA _ _ hr1b; have := opnd_lt' hA g hg_lt (1 - b); omega
    have hu1b : u ∈ side (n := n) C g (1 - b) :=
      (mem_orIn n C hA (opnd C g (1 - b)) (by have := opnd_lt' hA g hg_lt (1 - b); omega) u).mpr
        (hr1b.trans ((mem_orIn n C hA (n + h) (by omega) u).mp hu))
    have : u ∈ wmax G C g ∩ side (n := n) C g (1 - b) := Finset.mem_inter.mpr ⟨hsubW hu, hu1b⟩
    rw [hW1b] at this; exact Finset.notMem_empty _ this
  have hhb_not_Cgcl : hb ∉ Cgcl := by
    intro hmem
    have hsubW := (hCgcl_subW hb hmem).2
    exact hv_notW (hsubW (by change v ∈ orIn n C (opnd C g b) at hv_b; rwa [hhb_eq] at hv_b))
  have hcg_total : Cg1b.card + 1 + Cgcl.card ≤ (coneGates G C g).card := by
    have hsub : insert hb (Cg1b ∪ Cgcl) ⊆ coneGates G C g :=
      Finset.insert_subset hhb_cg (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem (by simp [hhb_not_Cg1b, hhb_not_Cgcl]),
      Finset.card_union_of_disjoint hCgcl_disj_Cg1b.symm] at hcard
    omega
  have hmix_witness_uniq : ∀ (m : ℕ), m ∈ mixing G C → n + g ∈ (gateAt C m).inputs →
      ∀ (a1 a2 : ℕ) (b1 b2 : Fin 2) (w1 w2 : Fin n),
      a1 ∈ tops G C → OrReaches n C (opnd C a1 b1) m → w1 ∈ side (n := n) C a1 (1 - b1) → w1 ∈ wmax G C g →
      a2 ∈ tops G C → OrReaches n C (opnd C a2 b2) m → w2 ∈ side (n := n) C a2 (1 - b2) → w2 ∈ wmax G C g →
      w1 = w2 := by
    intro m hm hgm a1 a2 b1 b2 w1 w2 ha1 hr1 hw1s hw1W ha2 hr2 hw2s hw2W
    have hm_lt : m < C.gates.length := by
      simp only [mixing, orN, gatesWhere, Finset.mem_filter, Finset.mem_range] at hm; exact hm.1.1
    obtain ⟨_, y0, y1, hmin, _, _⟩ := hA m hm_lt
    have hex_y : ∃ y ∈ (gateAt C m).inputs, y ≠ n + g := by
      have hm_xor : (orIn n C (opnd C m 0) = ∅) ≠ (orIn n C (opnd C m 1) = ∅) := (Finset.mem_filter.mp hm).2
      have h0eq : opnd C m 0 = y0 := by simp [opnd, hmin]
      have h1eq : opnd C m 1 = y1 := by simp [opnd, hmin]
      rw [h0eq, h1eq] at hm_xor
      rw [hmin] at hgm ⊢
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hgm ⊢
      rcases hgm with rfl | rfl
      · refine ⟨y1, Or.inr rfl, fun heq => hm_xor (by rw [heq])⟩
      · refine ⟨y0, Or.inl rfl, fun heq => hm_xor (by rw [heq])⟩
    obtain ⟨y, hy_in, hy_ne⟩ := hex_y
    obtain ⟨⟨um, hum_y, hum_g⟩, hrest⟩ := thm_1506 n G C h4 hE hL hT g hg m hm hgm y hy_in hy_ne
    have hum_nev : um ≠ v := by
      intro heq; subst um
      have hgv : gateVal n C g (pairInput v v) = true := by
        rw [← W_eq_gateVal, hgeval]
        exact ⟨⟨v, hv0, by simp [pairInput]⟩, ⟨v, hv1, by simp [pairInput]⟩⟩
      rw [hgv] at hum_g; exact Bool.noConfusion hum_g
    have hadj_of_sides : ∀ a ∈ tops G C, ∀ t : Fin 2, ∀ x ∈ side (n := n) C a t, ∀ z ∈ side (n := n) C a (1 - t),
        G.Adj x z := by
      intro a ha t x hx z hz
      simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha
      have hW0 := orR_mono n C hA (pairInput x z) (opnd C a t) x.val
        ((mem_orIn n C hA _ (by have := opnd_lt' hA a ha.1 t; omega) x).mp hx)
        (by rw [M1528.P2.W_input n C _ x.val x.isLt]; simp [pairInput])
      have hW1 := orR_mono n C hA (pairInput x z) (opnd C a (1 - t)) z.val
        ((mem_orIn n C hA _ (by have := opnd_lt' hA a ha.1 (1 - t); omega) z).mp hz)
        (by rw [M1528.P2.W_input n C _ z.val z.isLt]; simp [pairInput])
      have hWa : W n C (pairInput x z) (n + a) = true := by
        rw [W_and n C _ a ha.1 ha.2.1 (opnd C a 0) (opnd C a 1) (opnd_eq n C hA a ha.1)
          (opnd_lt' hA a ha.1 0) (opnd_lt' hA a ha.1 1), Bool.and_eq_true]
        rcases fin2_cases t with rfl | rfl <;> [exact ⟨hW0, hW1⟩; exact ⟨hW1, hW0⟩]
      have hF := ha.2.2 (pairInput x z) hWa
      rwa [graphFun_pair] at hF
    have hum1 := (hrest um hum_y a1 ha1 b1 hr1).1
    have hum2 := (hrest um hum_y a2 ha2 b2 hr2).1
    have h1 := hadj_of_sides a1 ha1 b1 um hum1 w1 hw1s
    have h2 := hadj_of_sides a2 ha2 b2 um hum2 w2 hw2s
    exact Finset.card_le_one.mp (hW_clause4 um hum_nev) w1
      (Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩, hw1W⟩)
      w2
      (Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩, hw2W⟩)
  have hwmix_ex : ∀ w ∈ Wmix, ∃ m ∈ mixing G C, n + g ∈ (gateAt C m).inputs ∧
      ∃ a ∈ tops G C, ∃ ba : Fin 2, OrReaches n C (opnd C a ba) m ∧ w ∈ side (n := n) C a (1 - ba) := by
    intro w hw
    obtain ⟨hwU, hw_notCL⟩ := Finset.mem_sdiff.mp hw
    obtain ⟨hwW, hw_ustar⟩ := Finset.mem_filter.mp hwU
    have hwv : G.Adj w v := (hv_adj_W w hwW).symm
    obtain ⟨_, _, htri⟩ := ustar_edge_structure G C h4 hE hL hT g hg w v hwv hw_ustar
    rcases htri with ⟨a, haCL, ba, hbag, hsubW, hwv_side⟩ | ⟨a, ha_top, _, ba, _, m, hm, hm_reach, hgm,
        _, _, _, _, _, _, _, z, hzW, _, hz_eq, hz_side, _, _⟩
    · exfalso
      apply hw_notCL
      refine Finset.mem_filter.mpr ⟨hwU, a, haCL, ba, hbag, ?_⟩
      rcases hwv_side with h | h
      · exact h
      · exact absurd (hsubW h) hv_notW
    · have hzw : z = w := by
        rcases hz_eq with h | h
        · exact h
        · exact absurd (h ▸ hzW) hv_notW
      subst z
      exact ⟨m, hm, hgm, a, ha_top, ba, hm_reach, hz_side⟩
  let fmix : Fin n → ℕ := fun w => if h : w ∈ Wmix then (hwmix_ex w h).choose else 0
  have hfmix_mem : ∀ w ∈ Wmix, fmix w ∈ mixing G C := fun w hw => by
    simp only [fmix, hw, ↓reduceDIte]; exact (hwmix_ex w hw).choose_spec.1
  have hfmix_inj : Set.InjOn fmix Wmix := by
    intro w1 hw1 w2 hw2 heq
    have h1 := (hwmix_ex w1 hw1).choose_spec
    have h2 := (hwmix_ex w2 hw2).choose_spec
    have hm1eq : fmix w1 = (hwmix_ex w1 hw1).choose := by dsimp only [fmix]; split_ifs <;> first | rfl | contradiction
    have hm2eq : fmix w2 = (hwmix_ex w2 hw2).choose := by dsimp only [fmix]; split_ifs <;> first | rfl | contradiction
    have hmeq : (hwmix_ex w1 hw1).choose = (hwmix_ex w2 hw2).choose := by rw [← hm1eq, ← hm2eq, heq]
    obtain ⟨hm1, hgm1, a1, ha1, b1, hr1, hs1⟩ := h1
    obtain ⟨hm2, hgm2, a2, ha2, b2, hr2, hs2⟩ := h2
    rw [← hmeq] at hr2
    have hw1W : w1 ∈ wmax G C g := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hw1).1).1
    have hw2W : w2 ∈ wmax G C g := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hw2).1).1
    exact hmix_witness_uniq _ hm1 hgm1 a1 a2 b1 b2 w1 w2 ha1 hr1 hs1 hw1W ha2 hr2 hs2 hw2W
  have hWmix_le : Wmix.card ≤ (mixing G C).card := by
    have hsub : Wmix.image fmix ⊆ mixing G C := by
      intro m hm; obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hm; exact hfmix_mem w hw
    rw [← Finset.card_image_of_injOn hfmix_inj]
    exact Finset.card_le_card hsub
  have hXcov : ∀ e ∈ Ustar G C, ∃ z ∈ K ∪ {v, wP}, z ∈ e := by
    intro e he
    rw [hU_eq, Finset.mem_union] at he
    rcases he with h1 | h2
    · obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp h1
      exact ⟨wP, Finset.mem_union_right _ (by simp), Sym2.mem_mk_left _ _⟩
    · obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp h2
      exact ⟨v, Finset.mem_union_right _ (by simp), Sym2.mem_mk_right _ _⟩
  have hxcard : (({v, wP} : Finset (Fin n)) \ K).card ≤ 2 :=
    (Finset.card_le_card Finset.sdiff_subset).trans Finset.card_le_two
  apply cover_of_budget G C g K hKcov h1528 {v, wP} hXcov
  omega

lemma cover_with_singletons {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (h4 : NoFourCycle G) (hE : G.edgeFinset.Nonempty)
    (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g})
    (K : Finset (Fin n))
    (hKcov : ∀ e ∈ starEdges G C, ∃ v ∈ K, v ∈ e)
    (hformU : formU G C g ⊆ K) (hformZ : formZ G C g ⊆ K)
    (h1528 : G.edgeFinset.card + K.card + (pen G C g K).card + 1 +
      (mixing G C).card + 2 * (centreless G C).card + (coneGates G C g).card ≤
      C.size + (Ustar G C).card + 1)
    (hUne : (Ustar G C).Nonempty)
    (hIne : (side (n := n) C g 0 ∩ side (n := n) C g 1).Nonempty) :
    ∃ T : Finset (Fin n), (∀ e ∈ G.edgeFinset, ∃ v ∈ T, v ∈ e) ∧
      G.edgeFinset.card + T.card ≤ C.size + 1 := by
  classical
  obtain ⟨hPne, hQne, hgeval, hW_iff, _, _, _, _, _⟩ := g_semantics G C hL hT g hg
  by_cases hP1 : (side (n := n) C g 0).card ≤ 1
  · obtain ⟨v, hvI⟩ := hIne
    have hv0 : v ∈ side (n := n) C g 0 := (Finset.mem_inter.mp hvI).1
    have hv1 : v ∈ side (n := n) C g 1 := (Finset.mem_inter.mp hvI).2
    have hPeq : side (n := n) C g 0 = {v} := by
      obtain ⟨x, hx⟩ := Finset.card_eq_one.mp (le_antisymm hP1 (Finset.card_pos.mpr hPne))
      have : v = x := by rw [hx, Finset.mem_singleton] at hv0; exact hv0
      rw [hx, this]
    exfalso
    refine replace_gate_by_wire G C hE hL hT g hg v.val (by have := v.isLt; omega) ?_ (Or.inl ?_)
    · intro x y huv hU
      obtain ⟨hgtrue, _, _⟩ := ustar_edge_structure G C h4 hE hL hT g hg x y huv hU
      rw [← W_eq_gateVal, hgeval, hPeq] at hgtrue
      obtain ⟨⟨p, hp, hpx⟩, _⟩ := hgtrue
      rw [Finset.mem_singleton] at hp; subst p
      rw [W_input n C _ v.val v.isLt]; exact hpx
    · intro x hxv
      rw [W_input n C x v.val v.isLt] at hxv
      rw [hgeval]; exact ⟨⟨v, hv0, hxv⟩, ⟨v, hv1, hxv⟩⟩
  by_cases hQ1 : (side (n := n) C g 1).card ≤ 1
  · obtain ⟨v, hvI⟩ := hIne
    have hv0 : v ∈ side (n := n) C g 0 := (Finset.mem_inter.mp hvI).1
    have hv1 : v ∈ side (n := n) C g 1 := (Finset.mem_inter.mp hvI).2
    have hQeq : side (n := n) C g 1 = {v} := by
      obtain ⟨x, hx⟩ := Finset.card_eq_one.mp (le_antisymm hQ1 (Finset.card_pos.mpr hQne))
      have : v = x := by rw [hx, Finset.mem_singleton] at hv1; exact hv1
      rw [hx, this]
    exfalso
    refine replace_gate_by_wire G C hE hL hT g hg v.val (by have := v.isLt; omega) ?_ (Or.inl ?_)
    · intro x y huv hU
      obtain ⟨hgtrue, _, _⟩ := ustar_edge_structure G C h4 hE hL hT g hg x y huv hU
      rw [← W_eq_gateVal, hgeval, hQeq] at hgtrue
      obtain ⟨_, ⟨q, hq, hqx⟩⟩ := hgtrue
      rw [Finset.mem_singleton] at hq; subst q
      rw [W_input n C _ v.val v.isLt]; exact hqx
    · intro x hxv
      rw [W_input n C x v.val v.isLt] at hxv
      rw [hgeval]; exact ⟨⟨v, hv0, hxv⟩, ⟨v, hv1, hxv⟩⟩
  have hP2 : 2 ≤ (side (n := n) C g 0).card := by omega
  have hQ2 : 2 ≤ (side (n := n) C g 1).card := by omega
  by_cases hI2 : 2 ≤ (side (n := n) C g 0 ∩ side (n := n) C g 1).card
  · exact cover_inter_ge_two G h4 hE C hL hT g hg K hKcov h1528 hUne hI2
  have hI1 : (side (n := n) C g 0 ∩ side (n := n) C g 1).card = 1 :=
    le_antisymm (by omega) (Finset.card_pos.mpr hIne)
  obtain ⟨v, hInter⟩ := Finset.card_eq_one.mp hI1
  have h1529 := thm_1529 n G h4 (side (n := n) C g 0) (side (n := n) C g 1) (wmax G C g) hW_iff
  have h1530 := thm_1530 n G h4 (side (n := n) C g 0) (side (n := n) C g 1) (wmax G C g) hW_iff
  have hv_mem : v ∈ side (n := n) C g 0 ∩ side (n := n) C g 1 := by rw [hInter]; simp
  by_cases hWP : (wmax G C g ∩ side (n := n) C g 0).Nonempty
  · obtain ⟨wP, hwP_eq⟩ := Finset.card_eq_one.mp (le_antisymm (h1530.1 hQ2) (Finset.card_pos.mpr hWP))
    have hwPW : wP ∈ wmax G C g := (Finset.mem_inter.mp (by rw [hwP_eq]; simp)).1
    have hwPP : wP ∈ side (n := n) C g 0 := (Finset.mem_inter.mp (by rw [hwP_eq]; simp)).2
    have hWQ_empty : wmax G C g ∩ side (n := n) C g 1 = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro wQ hwQ
      obtain ⟨hwQW, hwQQ⟩ := Finset.mem_inter.mp hwQ
      have hadj := (h1529.1 wP hwPW hwPP).2 wQ hwQQ
      exact htri v wP wQ (h1529.2.2.1 v hv_mem wP hwPW) hadj
        (h1529.2.2.1 v hv_mem wQ hwQW).symm
    exact cover_inter_one_side G htri h4 hE C hL hT g hg K hKcov hformU hformZ h1528
      v hInter 0 wP hwP_eq hWQ_empty
  · rw [Finset.not_nonempty_iff_eq_empty] at hWP
    by_cases hWQ : (wmax G C g ∩ side (n := n) C g 1).Nonempty
    · obtain ⟨wQ, hwQ_eq⟩ := Finset.card_eq_one.mp (le_antisymm (h1530.2.1 hP2) (Finset.card_pos.mpr hWQ))
      exact cover_inter_one_side G htri h4 hE C hL hT g hg K hKcov hformU hformZ h1528
        v hInter 1 wQ hwQ_eq hWP
    · rw [Finset.not_nonempty_iff_eq_empty] at hWQ
      exfalso
      refine replace_gate_by_wire G C hE hL hT g hg v.val (by have := v.isLt; omega) ?_ (Or.inl ?_)
      · intro x y hxy hU
        obtain ⟨hgtrue, hxyW, _⟩ := ustar_edge_structure G C h4 hE hL hT g hg x y hxy hU
        obtain ⟨h0, h1⟩ := g_pair_sides G C hL hT g hg x y hgtrue
        have hv_xy : x = v ∨ y = v := by
          rcases hxyW with hxW | hyW
          · have hx_notP : x ∉ side (n := n) C g 0 := fun h => by
              have : x ∈ wmax G C g ∩ side (n := n) C g 0 := Finset.mem_inter.mpr ⟨hxW, h⟩
              rw [hWP] at this; exact Finset.notMem_empty _ this
            have hx_notQ : x ∉ side (n := n) C g 1 := fun h => by
              have : x ∈ wmax G C g ∩ side (n := n) C g 1 := Finset.mem_inter.mpr ⟨hxW, h⟩
              rw [hWQ] at this; exact Finset.notMem_empty _ this
            have hyI := (h1530.2.2.1 x y hxy h0 h1 hxW).2.2 hx_notP hx_notQ
            rw [hInter, Finset.mem_singleton] at hyI
            exact Or.inr hyI
          · have hy_notP : y ∉ side (n := n) C g 0 := fun h => by
              have : y ∈ wmax G C g ∩ side (n := n) C g 0 := Finset.mem_inter.mpr ⟨hyW, h⟩
              rw [hWP] at this; exact Finset.notMem_empty _ this
            have hy_notQ : y ∉ side (n := n) C g 1 := fun h => by
              have : y ∈ wmax G C g ∩ side (n := n) C g 1 := Finset.mem_inter.mpr ⟨hyW, h⟩
              rw [hWQ] at this; exact Finset.notMem_empty _ this
            have hxI := (h1530.2.2.1 y x hxy.symm h0.symm h1.symm hyW).2.2 hy_notP hy_notQ
            rw [hInter, Finset.mem_singleton] at hxI
            exact Or.inl hxI
        rw [W_input n C _ v.val v.isLt, pairInput_true]
        rcases hv_xy with rfl | rfl <;> [exact Or.inl rfl; exact Or.inr rfl]
      · intro x hxv
        rw [W_input n C x v.val v.isLt] at hxv
        rw [hgeval]
        exact ⟨⟨v, (Finset.mem_inter.mp hv_mem).1, hxv⟩, ⟨v, (Finset.mem_inter.mp hv_mem).2, hxv⟩⟩
lemma one_junk_cover_all {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g : ℕ) (h4 : NoFourCycle G)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hL : IsLeastAO G C) (hT : TopForm G C) (hg : junk G C = {g}) :
    ∃ T : Finset (Fin n), (∀ e ∈ G.edgeFinset, ∃ v ∈ T, v ∈ e) ∧
      G.edgeFinset.card + T.card ≤ C.size + 1 := by
  classical
  by_cases hsil : ∀ u : Fin n, gateVal n C g (pairInput u u) = false
  · exact one_junk_cover G C g h4 htri hL hT hg hsil
  have hIne : (side (n := n) C g 0 ∩ side (n := n) C g 1).Nonempty := by
    push Not at hsil
    obtain ⟨u, hu⟩ := hsil
    have hu' : gateVal n C g (pairInput u u) = true := by
      cases h : gateVal n C g (pairInput u u) <;> simp_all
    rw [← W_eq_gateVal] at hu'
    obtain ⟨⟨v, hv, hvu⟩, ⟨w, hw, hwu⟩⟩ :=
      ((g_semantics G C hL hT g hg).2.2.1 (pairInput u u)).mp hu'
    have hv_eq : v = u := by simpa [pairInput] using hvu
    have hw_eq : w = u := by simpa [pairInput] using hwu
    subst v
    subst w
    exact ⟨u, Finset.mem_inter.mpr ⟨hv, hw⟩⟩
  by_cases hE : G.edgeFinset.Nonempty
  · obtain ⟨K, hKcov, hformU, hformZ, h1528⟩ := thm_1528 n G C h4 hE hL hT g hg
    by_cases hUne : (Ustar G C).Nonempty
    · exact cover_with_singletons G htri h4 hE C hL hT g hg K hKcov hformU hformZ h1528 hUne hIne
    · have hU0 : Ustar G C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hUne
      refine ⟨K, ?_, ?_⟩
      · intro e he
        apply hKcov e
        by_contra hs
        have hu : e ∈ Ustar G C := Finset.mem_sdiff.mpr ⟨he, hs⟩
        rw [hU0] at hu
        exact Finset.notMem_empty _ hu
      · rw [hU0, Finset.card_empty] at h1528
        omega
  · have hE0 : G.edgeFinset = ∅ := Finset.not_nonempty_iff_eq_empty.mp hE
    refine ⟨∅, ?_, ?_⟩
    · intro e he
      rw [hE0] at he
      exact (Finset.notMem_empty _ he).elim
    · rw [hE0]
      simp

lemma least_single_junk_cover {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h4 : NoFourCycle G)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hL : IsLeastAO G C) (hg : (junk G C).card = 1) :
    ∃ T : Finset (Fin n), (∀ e ∈ G.edgeFinset, ∃ v ∈ T, v ∈ e) ∧
      G.edgeFinset.card + T.card ≤ C.size + 1 := by
  classical
  by_cases hE : G.edgeFinset.Nonempty
  · obtain ⟨D, hLD, hsz, hJ, hTD⟩ := thm_1501 n G C hE hL
    obtain ⟨g, hgj⟩ := Finset.card_eq_one.mp (hJ.trans hg)
    obtain ⟨T, hTc, hTs⟩ := one_junk_cover_all G D g h4 htri hLD hTD hgj
    exact ⟨T, hTc, by rwa [hsz] at hTs⟩
  · have hE0 : G.edgeFinset = ∅ := Finset.not_nonempty_iff_eq_empty.mp hE
    refine ⟨∅, ?_, ?_⟩
    · intro e he
      rw [hE0] at he
      exact (Finset.notMem_empty _ he).elim
    · rw [hE0]
      simp

end PEqualNP.Outside.L_meta_2448_aux.oneJunk


-- Scratch prototype using outside modules; these are not approved final dependencies.
namespace PEqualNP.Outside.L_meta_2448.StarCoverPrototype
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.Outside.L_meta_2448_aux.foundation
open PEqualNP.Outside.L_meta_2448_aux.foundation.Close
open PEqualNP.Outside.L_meta_2448_aux.foundation.M1528.P1.S98

lemma orTree_all_or (base : ℕ) (ws : List ℕ) :
    ∀ g ∈ (orTreeGates base ws).1, g.op = GateOp.or := by
  induction ws with
  | nil => simp [orTreeGates]
  | cons w ws ih =>
    cases ws with
    | nil => simp [orTreeGates]
    | cons u us =>
      intro g hg
      simp only [orTreeGates, List.mem_append, List.mem_singleton] at hg
      rcases hg with hg | rfl
      · exact ih g hg
      · rfl

theorem star_cover_witness {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hE : G.edgeFinset.Nonempty)
    (K0 : Finset (Fin n)) (hcov : ∀ e ∈ G.edgeFinset, ∃ v ∈ K0, v ∈ e) :
    ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧
      HasStarProfile n G D ∧ D.size + 1 ≤ G.edgeFinset.card + K0.card := by
  classical
  let owner : Sym2 (Fin n) → Fin n := fun e =>
    if h : e ∈ G.edgeFinset then (hcov e h).choose else (hE.choose.out).1
  have howner_mem : ∀ e (he : e ∈ G.edgeFinset), owner e ∈ K0 ∧ owner e ∈ e := by
    intro e he
    simp only [owner, dite_eq_left, he]
    exact (hcov e he).choose_spec
  let L : Fin n → Finset (Fin n) := fun v =>
    Finset.univ.filter fun u => ∃ h : s(v, u) ∈ G.edgeFinset, owner s(v, u) = v
  have hL_adj : ∀ v u, u ∈ L v → G.Adj v u := by
    intro v u hu
    simp only [L, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    exact SimpleGraph.mem_edgeFinset.mp hu.1
  have hL_edge_iff : ∀ u v, G.Adj u v → (v ∈ L u ∨ u ∈ L v) ∧ (u ∈ K0 ∧ v ∈ L u ∨ v ∈ K0 ∧ u ∈ L v) := by
    intro u v huv
    have he : s(u, v) ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.mpr huv
    obtain ⟨hK, hmem⟩ := howner_mem s(u, v) he
    rcases Sym2.mem_iff.mp hmem with h | h
    · have hu : v ∈ L u := by
        simp only [L, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨he, h⟩
      exact ⟨Or.inl hu, Or.inl ⟨h ▸ hK, hu⟩⟩
    · have hv : u ∈ L v := by
        simp only [L, Finset.mem_filter, Finset.mem_univ, true_and]
        have he' : s(v, u) ∈ G.edgeFinset := by rw [Sym2.eq_swap]; exact he
        exact ⟨he', by rw [Sym2.eq_swap]; exact h⟩
      exact ⟨Or.inr hv, Or.inr ⟨h ▸ hK, hv⟩⟩
  have hsum : (∑ v ∈ K0, (L v).card) = G.edgeFinset.card := by
    have hbij : (K0.sigma L).card = G.edgeFinset.card := by
      refine Finset.card_bij (fun p _ => s(p.1, p.2)) ?_ ?_ ?_
      · intro p hp
        simp only [Finset.mem_sigma] at hp
        exact SimpleGraph.mem_edgeFinset.mpr (hL_adj p.1 p.2 hp.2)
      · intro p1 hp1 p2 hp2 heq
        simp only [Finset.mem_sigma, L, Finset.mem_filter, Finset.mem_univ, true_and] at hp1 hp2
        have h1 : p1.1 = p2.1 := by
          rw [← hp1.2.2, heq, hp2.2.2]
        have h2 : p1.2 = p2.2 := by
          have : s(p1.1, p1.2) = s(p1.1, p2.2) := by rw [← h1] at heq; exact heq
          rcases Sym2.eq_iff.mp this with ⟨_, hb⟩ | ⟨_, hb⟩
          · exact hb
          · have hadj : G.Adj p1.1 p1.2 := SimpleGraph.mem_edgeFinset.mp hp1.2.1
            rw [hb] at hadj
            exact (G.irrefl hadj).elim
        exact Sigma.ext h1 (heq_of_eq h2)
      · intro e he
        induction e using Sym2.ind with
        | _ u v =>
          have huv := SimpleGraph.mem_edgeFinset.mp he
          rcases (hL_edge_iff u v huv).2 with ⟨huK, hvL⟩ | ⟨hvK, huL⟩
          · exact ⟨⟨u, v⟩, Finset.mem_sigma.mpr ⟨huK, hvL⟩, rfl⟩
          · exact ⟨⟨v, u⟩, Finset.mem_sigma.mpr ⟨hvK, huL⟩, Sym2.eq_swap⟩
    rw [Finset.card_sigma] at hbij
    exact hbij
  let M := K0.filter fun v => (L v).Nonempty
  have hM_sub : M ⊆ K0 := Finset.filter_subset _ _
  have hM_ne : M.Nonempty := by
    obtain ⟨e, he⟩ := hE
    induction e using Sym2.ind with
    | _ u v =>
      rcases (hL_edge_iff u v (SimpleGraph.mem_edgeFinset.mp he)).2 with ⟨huK, hvL⟩ | ⟨hvK, huL⟩
      · exact ⟨u, Finset.mem_filter.mpr ⟨huK, ⟨v, hvL⟩⟩⟩
      · exact ⟨v, Finset.mem_filter.mpr ⟨hvK, ⟨u, huL⟩⟩⟩
  have hsumM : (∑ v ∈ M, (L v).card) = G.edgeFinset.card := by
    rw [← hsum]
    refine Finset.sum_subset hM_sub ?_
    intro v hv hnotM
    simp only [M, Finset.mem_filter, not_and, Finset.not_nonempty_iff_eq_empty] at hnotM
    rw [hnotM hv, Finset.card_empty]
  let buildStars : List (Fin n) → List Gate × List ℕ :=
    List.foldl (fun (acc : List Gate × List ℕ) (v : Fin n) =>
      let ws := (L v).toList.map Fin.val
      let (gs, out) := orTreeGates (n + acc.1.length) ws
      let andGate : Gate := ⟨GateOp.and, [v.val, out]⟩
      let andWire := n + acc.1.length + gs.length
      (acc.1 ++ gs ++ [andGate], acc.2 ++ [andWire])) ([], [])
  have hbuild_aux : ∀ (vs : List (Fin n)), (∀ v ∈ vs, (L v).Nonempty) →
      let res := buildStars vs
      res.1.length = (vs.map fun v => (L v).card).sum ∧
      res.2.length = vs.length ∧
      (∀ w ∈ res.2, w < n + res.1.length) ∧
      AO n ⟨res.1, 0⟩ ∧
      (∀ x : Fin n → Bool, ∀ w ∈ res.2, W n ⟨res.1, 0⟩ x w = true →
        ∃ v ∈ vs, x v = true ∧ ∃ u ∈ L v, x u = true) ∧
      (∀ x : Fin n → Bool, ∀ v ∈ vs, x v = true → (∃ u ∈ L v, x u = true) →
        ∃ w ∈ res.2, W n ⟨res.1, 0⟩ x w = true) := by
    intro vs
    induction vs using List.reverseRecOn with
    | nil =>
      intro _
      simp [buildStars, AO]
    | append_singleton vs v ih =>
      intro hne
      have hne_vs : ∀ u ∈ vs, (L u).Nonempty := fun u hu => hne u (by simp [hu])
      have hne_v : (L v).Nonempty := hne v (by simp)
      obtain ⟨hlen, hlen2, hlt, hAO, hsound, hcomp⟩ := ih hne_vs
      set acc := buildStars vs
      set ws := (L v).toList.map Fin.val
      have hws_ne : ws ≠ [] := by
        simp only [ws, ne_eq, List.map_eq_nil_iff, Finset.toList_eq_nil]
        exact Finset.nonempty_iff_ne_empty.mp hne_v
      have hws_lt : ∀ w ∈ ws, w < n + acc.1.length := by
        intro w hw
        simp only [ws, List.mem_map] at hw
        obtain ⟨u, _, rfl⟩ := hw
        have := u.isLt; omega
      set ot := orTreeGates (n + acc.1.length) ws
      have hot_len : ot.1.length + 1 = (L v).card := by
        have := orTreeGates_length (n + acc.1.length) ws hws_ne
        simpa [ot, ws] using this
      have hot_out_lt : ot.2 < n + acc.1.length + ot.1.length :=
        orTreeGates_out_lt (n + acc.1.length) ws hws_ne hws_lt
      let andGate : Gate := ⟨GateOp.and, [v.val, ot.2]⟩
      let andWire := n + acc.1.length + ot.1.length
      let newGs := acc.1 ++ ot.1 ++ [andGate]
      have hbuild_eq : buildStars (vs ++ [v]) = (newGs, acc.2 ++ [andWire]) := by
        simp [buildStars, List.foldl_append, acc, newGs, ot, ws, andGate, andWire]
      rw [hbuild_eq]
      have hnewLen : newGs.length = acc.1.length + (L v).card := by
        simp only [newGs, List.length_append, List.length_singleton]
        omega
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [hnewLen, hlen]
      · simp [hlen2]
      · intro w hw
        simp only [List.mem_append, List.mem_singleton] at hw
        rcases hw with hw | rfl
        · have h1 := hlt w hw
          have h2 : newGs.length = acc.1.length + (L v).card := hnewLen
          change w < n + newGs.length
          omega
        · simp only [andWire, newGs, List.length_append, List.length_singleton]; omega
      · intro k hk
        have hAO_ot := (orTreeGates_eval n acc.1 ws hws_ne hws_lt (fun _ => false)).1
        by_cases hk1 : k < acc.1.length
        · have hg : gateAt ⟨newGs, 0⟩ k = gateAt ⟨acc.1, 0⟩ k := by
            rw [gateAt_eq ⟨newGs, 0⟩ k hk, gateAt_eq ⟨acc.1, 0⟩ k hk1]
            simp only [newGs, List.append_assoc]
            exact List.getElem_append_left hk1
          rw [hg]; exact hAO k hk1
        · by_cases hk2 : k < acc.1.length + ot.1.length
          · have hidx : k - acc.1.length < ot.1.length := by omega
            have hg : gateAt ⟨newGs, 0⟩ k = ot.1[k - acc.1.length]'hidx := by
              rw [gateAt_eq ⟨newGs, 0⟩ k hk]
              simp only [newGs]
              rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by omega)]
            rw [hg]
            obtain ⟨hop, a, b, hin, ha, hb⟩ := hAO_ot (k - acc.1.length) hidx
            exact ⟨Or.inr hop, a, b, hin, by omega, by omega⟩
          · have hkeq : k = acc.1.length + ot.1.length := by
              simp only [newGs, List.length_append, List.length_singleton] at hk; omega
            subst hkeq
            have hg : gateAt ⟨newGs, 0⟩ (acc.1.length + ot.1.length) = andGate := by
              rw [gateAt_eq ⟨newGs, 0⟩ _ hk]
              simp [newGs]
            rw [hg]
            exact ⟨Or.inl rfl, v.val, ot.2, rfl, by have := v.isLt; omega, by omega⟩
      · intro x w hw hW
        have hpre_eq : ∀ u, u < n + acc.1.length → W n ⟨newGs, 0⟩ x u = W n ⟨acc.1, 0⟩ x u := by
          intro u hu
          have := prefix_W n acc.1 (ot.1 ++ [andGate]) [] 0 0 x u hu
          simpa [newGs, List.append_assoc] using this
        simp only [List.mem_append, List.mem_singleton] at hw
        rcases hw with hw | rfl
        · rw [hpre_eq w (hlt w hw)] at hW
          obtain ⟨u0, hu0, hxu0, z, hzL, hxz⟩ := hsound x w hw hW
          exact ⟨u0, by simp [hu0], hxu0, z, hzL, hxz⟩
        · have hk : acc.1.length + ot.1.length < newGs.length := by
            simp [newGs]
          have hg : gateAt ⟨newGs, 0⟩ (acc.1.length + ot.1.length) = andGate := by
            rw [gateAt_eq ⟨newGs, 0⟩ _ hk]; simp [newGs]
          have hadd : andWire = n + (acc.1.length + ot.1.length) := by simp [andWire]; omega
          rw [hadd, W_and n ⟨newGs, 0⟩ x _ hk (by rw [hg]) v.val ot.2 (by rw [hg])
            (by have := v.isLt; omega) (by omega), Bool.and_eq_true] at hW
          rw [W_input n ⟨newGs, 0⟩ x v.val v.isLt] at hW
          have hot_eq : W n ⟨newGs, 0⟩ x ot.2 = W n ⟨acc.1 ++ ot.1, ot.2⟩ x ot.2 := by
            have := prefix_W n (acc.1 ++ ot.1) [andGate] [] 0 ot.2 x ot.2
              (by simp; omega)
            simpa [newGs] using this
          rw [hot_eq, (orTreeGates_eval n acc.1 ws hws_ne hws_lt x).2] at hW
          obtain ⟨uval, huval, hWu⟩ := hW.2
          simp only [ws, List.mem_map, Finset.mem_toList] at huval
          obtain ⟨u, huL, rfl⟩ := huval
          rw [W_input n ⟨acc.1, 0⟩ x u.val u.isLt] at hWu
          exact ⟨v, by simp, hW.1, u, huL, hWu⟩
      · intro x v0 hv0 hxv0 ⟨u, huL, hxu⟩
        have hpre_eq : ∀ u', u' < n + acc.1.length → W n ⟨newGs, 0⟩ x u' = W n ⟨acc.1, 0⟩ x u' := by
          intro u' hu'
          have := prefix_W n acc.1 (ot.1 ++ [andGate]) [] 0 0 x u' hu'
          simpa [newGs, List.append_assoc] using this
        simp only [List.mem_append, List.mem_singleton] at hv0
        rcases hv0 with hv0 | rfl
        · obtain ⟨w, hw, hW⟩ := hcomp x v0 hv0 hxv0 ⟨u, huL, hxu⟩
          exact ⟨w, by simp [hw], by rw [hpre_eq w (hlt w hw)]; exact hW⟩
        · refine ⟨andWire, by simp, ?_⟩
          have hk : acc.1.length + ot.1.length < newGs.length := by simp [newGs]
          have hg : gateAt ⟨newGs, 0⟩ (acc.1.length + ot.1.length) = andGate := by
            rw [gateAt_eq ⟨newGs, 0⟩ _ hk]; simp [newGs]
          have hadd : andWire = n + (acc.1.length + ot.1.length) := by simp [andWire]; omega
          rw [hadd, W_and n ⟨newGs, 0⟩ x _ hk (by rw [hg]) v0.val ot.2 (by rw [hg])
            (by have := v0.isLt; omega) (by omega), Bool.and_eq_true,
            W_input n ⟨newGs, 0⟩ x v0.val v0.isLt]
          refine ⟨hxv0, ?_⟩
          have hot_eq : W n ⟨newGs, 0⟩ x ot.2 = W n ⟨acc.1 ++ ot.1, ot.2⟩ x ot.2 := by
            have := prefix_W n (acc.1 ++ ot.1) [andGate] [] 0 ot.2 x ot.2
              (by simp; omega)
            simpa [newGs] using this
          rw [hot_eq, (orTreeGates_eval n acc.1 ws hws_ne hws_lt x).2]
          refine ⟨u.val, List.mem_map.mpr ⟨u, Finset.mem_toList.mpr huL, rfl⟩, ?_⟩
          rw [W_input n ⟨acc.1, 0⟩ x u.val u.isLt]
          exact hxu
  let vs := M.toList
  have hvs_ne : ∀ v ∈ vs, (L v).Nonempty := by
    intro v hv
    simp only [vs, Finset.mem_toList, M, Finset.mem_filter] at hv
    exact hv.2
  obtain ⟨hlen1, hlen2, hlt, hAO1, hsound1, hcomp1⟩ := hbuild_aux vs hvs_ne
  set bs := buildStars vs
  have hbs2_ne : bs.2 ≠ [] := by
    intro h
    have h1 : vs.length = 0 := by rw [← hlen2, h]; rfl
    have : M = ∅ := by
      rw [← Finset.card_eq_zero, ← Finset.length_toList, h1]
    exact Finset.nonempty_iff_ne_empty.mp hM_ne this
  set top := orTreeGates (n + bs.1.length) bs.2
  let D : Circuit := ⟨bs.1 ++ top.1, top.2⟩
  have hD_AO : AO n D := by
    intro k hk
    have hAO_top := (orTreeGates_eval n bs.1 bs.2 hbs2_ne hlt (fun _ => false)).1
    by_cases hk1 : k < bs.1.length
    · have hg : gateAt D k = gateAt ⟨bs.1, 0⟩ k := by
        rw [gateAt_eq D k hk, gateAt_eq ⟨bs.1, 0⟩ k hk1]
        exact List.getElem_append_left hk1
      rw [hg]; exact hAO1 k hk1
    · have hidx : k - bs.1.length < top.1.length := by simp [D] at hk; omega
      have hg : gateAt D k = top.1[k - bs.1.length]'hidx := by
        rw [gateAt_eq D k hk]
        exact List.getElem_append_right (by omega)
      rw [hg]
      obtain ⟨hop, a, b, hin, ha, hb⟩ := hAO_top (k - bs.1.length) hidx
      exact ⟨Or.inr hop, a, b, hin, by omega, by omega⟩
  have hD_fun : circuitFun n D = graphFun G ∅ := by
    funext x
    rw [Bool.eq_iff_iff]
    have hDeval : circuitFun n D x = W n D x top.2 := rfl
    rw [hDeval, (orTreeGates_eval n bs.1 bs.2 hbs2_ne hlt x).2]
    constructor
    · rintro ⟨w, hw, hW⟩
      obtain ⟨v, hv, hxv, u, huL, hxu⟩ := hsound1 x w hw hW
      have hadj : G.Adj v u := hL_adj v u huL
      simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
        Bool.false_or, decide_eq_true_eq]
      exact ⟨v, u, hadj, hxv, hxu⟩
    · intro hG
      simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
        Bool.false_or, decide_eq_true_eq] at hG
      obtain ⟨u, v, hadj, hxu, hxv⟩ := hG
      rcases (hL_edge_iff u v hadj).2 with ⟨huK, hvL⟩ | ⟨hvK, huL⟩
      · have huM : u ∈ vs := by
          simp only [vs, Finset.mem_toList, M, Finset.mem_filter]
          exact ⟨huK, ⟨v, hvL⟩⟩
        exact hcomp1 x u huM hxu ⟨v, hvL, hxv⟩
      · have hvM : v ∈ vs := by
          simp only [vs, Finset.mem_toList, M, Finset.mem_filter]
          exact ⟨hvK, ⟨u, huL⟩⟩
        exact hcomp1 x v hvM hxv ⟨u, huL, hxu⟩
  have hD_size : D.size + 1 = G.edgeFinset.card + M.card := by
    have htop_len : top.1.length + 1 = bs.2.length :=
      orTreeGates_length (n + bs.1.length) bs.2 hbs2_ne
    have hsum_vs : (vs.map fun v => (L v).card).sum = G.edgeFinset.card := by
      rw [← hsumM]
      simp [vs]
    have hvs_len : vs.length = M.card := Finset.length_toList M
    have h1 : bs.1.length = G.edgeFinset.card := by rw [hlen1, hsum_vs]
    have h2 : bs.2.length = M.card := by rw [hlen2, hvs_len]
    simp only [Circuit.size, D, List.length_append]
    omega
  have hbuild_primary : ∀ vs, ∀ g ∈ (buildStars vs).1, g.op = GateOp.and →
      ∃ a : Fin n, a.val ∈ g.inputs := by
    intro vs
    induction vs using List.reverseRecOn with
    | nil => simp [buildStars]
    | append_singleton vs v ih =>
      intro g hg hop
      simp only [buildStars, List.foldl_append, List.foldl_cons, List.foldl_nil] at hg
      change g ∈ ((buildStars vs).1 ++
        (orTreeGates (n + (buildStars vs).1.length) ((L v).toList.map Fin.val)).1 ++
        [⟨GateOp.and, [v.val,
          (orTreeGates (n + (buildStars vs).1.length) ((L v).toList.map Fin.val)).2]⟩]) at hg
      rcases List.mem_append.mp hg with hg | hg
      · rcases List.mem_append.mp hg with hg | hg
        · exact ih g hg hop
        · have hor := orTree_all_or _ _ g hg
          rw [hop] at hor
          cases hor
      · simp only [List.mem_singleton] at hg
        subst g
        exact ⟨v, by simp⟩
  have hD_primary : ∀ j < D.gates.length, (gateAt D j).op = GateOp.and →
      ∃ a : Fin n, a.val ∈ (gateAt D j).inputs := by
    intro j hj hop
    have hmem : gateAt D j ∈ D.gates := by
      rw [gateAt_eq D j hj]
      exact List.getElem_mem hj
    change gateAt D j ∈ bs.1 ++ top.1 at hmem
    rcases List.mem_append.mp hmem with hmem | hmem
    · exact hbuild_primary vs _ hmem hop
    · have hor := orTree_all_or _ _ (gateAt D j) hmem
      rw [hop] at hor
      cases hor
  have hD_mono : Monotone2 D := by
    intro g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    have h := hD_AO j hj
    rw [gateAt_eq D j hj] at h
    obtain ⟨hop, a, b, hin, _, _⟩ := h
    constructor
    · simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hop
    · simp [hin]
  refine ⟨D, hD_mono, hD_fun,
    PEqualNP.Outside.L_meta_2448.cross.star_of_primary_operands G D hD_primary, ?_⟩
  have hM_le : M.card ≤ K0.card := Finset.card_le_card hM_sub
  omega

end PEqualNP.Outside.L_meta_2448.StarCoverPrototype

namespace PEqualNP.Outside.L_meta_2448_aux.oneJunkStar

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma mono_of_AO2 {n : ℕ} {C : Circuit} (h : IsAO2 n C) : Monotone2 C := by
  intro g hg
  constructor
  · simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h.1 g hg
  · rw [h.2.2 g hg]

end PEqualNP.Outside.L_meta_2448_aux.oneJunkStar

namespace PEqualNP.Outside.L_meta_2448_aux.oneJunkStar

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma star_of_no_junk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h4 : NoFourCycle G)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hmono : Monotone2 C) (hzero : (junk G C).card = 0) : HasStarProfile n G C := by
  classical
  apply PEqualNP.Outside.L_meta_2448.cross.star_of_proper_pair_sound n G C htri h4 hmono
  intro j hj hop u v _ hval
  by_contra huv
  have hfalse : graphFun G ∅ (pairInput u v) = false := by
    apply Bool.eq_false_iff.mpr
    intro ht
    exact huv ((PEqualNP.Outside.L_meta_2448_aux.foundation.M1528.P1.S90.graphFun_pair G u v).mp ht)
  have hmem : j ∈ junk G C := by
    simp only [junk, gatesWhere, Finset.mem_filter, Finset.mem_range]
    exact ⟨hj, hop, hj, pairInput u v, hval, hfalse⟩
  rw [Finset.card_eq_zero.mp hzero] at hmem
  exact Finset.notMem_empty _ hmem

lemma empty_graph_star_minimum {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hempty : G.edgeFinset = ∅) :
    ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧
      (∀ E : Circuit, Monotone2 E → circuitFun n E = graphFun G ∅ → D.size ≤ E.size) ∧
      HasStarProfile n G D := by
  let D : Circuit := ⟨[], n⟩
  have hno : ∀ u v : Fin n, ¬ G.Adj u v := by
    intro u v huv
    have hmem : s(u, v) ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.mpr huv
    rw [hempty] at hmem
    exact Finset.notMem_empty _ hmem
  have hfun : circuitFun n D = graphFun G ∅ := by
    funext x
    simp [D, circuitFun, Circuit.eval, Circuit.wires, graphFun, hno,
      List.getD_eq_getElem?_getD]
  refine ⟨D, ?_, hfun, ?_, ?_⟩
  · intro g hg
    cases hg
  · intro E _ _
    exact Nat.zero_le _
  · intro j hj
    exact (Nat.not_lt_zero j hj).elim

lemma posted_conclusion_of_at_most_one_junk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h4 : NoFourCycle G)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hAO : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (hmin : IsMinimalMonoCircuit n C) (hjunk : (junk G C).card ≤ 1) :
    ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧
      (∀ E : Circuit, Monotone2 E → circuitFun n E = graphFun G ∅ → D.size ≤ E.size) ∧
      HasStarProfile n G D := by
  classical
  by_cases hzero : (junk G C).card = 0
  · exact ⟨C, hmin.1, hfun, fun E hE hEf => hmin.2 E hE (hEf.trans hfun.symm),
      star_of_no_junk G C h4 htri hmin.1 hzero⟩
  by_cases hE : G.edgeFinset.Nonempty
  · have hL : IsLeastAO G C := ⟨hAO, hfun,
      fun E hE hEf => hmin.2 E (mono_of_AO2 hE) (hEf.trans hfun.symm)⟩
    have hjunk1 : (junk G C).card = 1 := by omega
    obtain ⟨K, hK, hbudget⟩ :=
      PEqualNP.Outside.L_meta_2448_aux.oneJunk.least_single_junk_cover G C h4 htri hL hjunk1
    obtain ⟨D, hD, hDf, hDs, hsize⟩ :=
      PEqualNP.Outside.L_meta_2448.StarCoverPrototype.star_cover_witness G hE K hK
    have hsz : D.size ≤ C.size := by omega
    exact ⟨D, hD, hDf, fun E hE hEf => hsz.trans (hmin.2 E hE (hEf.trans hfun.symm)), hDs⟩
  · exact empty_graph_star_minimum G (Finset.not_nonempty_iff_eq_empty.mp hE)

end PEqualNP.Outside.L_meta_2448_aux.oneJunkStar


namespace PEqualNP.Outside.L_meta_2448_aux.inputBound

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover


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

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

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

lemma dep (n : ℕ) (C : Circuit) (hR : ∀ j < C.gates.length, (gateAt C j).inputs.length ≤ 2) :
    ∀ k, k ≤ C.gates.length → ∀ W : Finset ℕ, (∀ w ∈ W, w < n + k) →
      ∃ T : Finset (Fin n), T.card ≤ k + W.card ∧
        ∀ x y : Fin n → Bool, (∀ i ∈ T, x i = y i) →
          ∀ w ∈ W, val C (List.ofFn x) w = val C (List.ofFn y) w := by
  intro k
  induction k with
  | zero =>
    intro _ W hW
    refine ⟨Finset.univ.filter (fun i : Fin n => (i : ℕ) ∈ W), ?_, ?_⟩
    · rw [Nat.zero_add, ← Finset.card_image_of_injective _ Fin.val_injective]
      apply Finset.card_le_card
      intro a ha
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ha
      exact (Finset.mem_filter.1 hi).2
    · intro x y h w hw
      have hw' : w < n := by simpa using hW w hw
      have e : ∀ z : Fin n → Bool, (List.ofFn z).getD w false = z ⟨w, hw'⟩ := by
        intro z; simp [List.getD_eq_getElem?_getD, hw']
      rw [val_input (by simp) hw', val_input (by simp) hw', e, e]
      exact h ⟨w, hw'⟩ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hw⟩)
  | succ k ih =>
    intro hk W hW
    by_cases hmem : n + k ∈ W
    · obtain ⟨W2, hW2⟩ : ∃ W2 : Finset ℕ, W2 = W.erase (n + k) ∪
          ((gateAt C k).inputs.filter (fun i => i < n + k)).toFinset := ⟨_, rfl⟩
      have hlt2 : ∀ w ∈ W2, w < n + k := by
        intro w hw
        rw [hW2] at hw
        rcases Finset.mem_union.1 hw with h | h
        · have h1 := hW w (Finset.mem_of_mem_erase h)
          have h2 := Finset.ne_of_mem_erase h
          omega
        · simp at h; exact h.2
      have hs1 : ∀ w ∈ W, w ≠ n + k → w ∈ W2 := by
        intro w hw hne
        rw [hW2]
        exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hne, hw⟩)
      have hs2 : ∀ i ∈ (gateAt C k).inputs, i < n + k → i ∈ W2 := by
        intro i hi hlt
        rw [hW2]
        exact Finset.mem_union_right _ (by simp [hi, hlt])
      have hc : W2.card + 1 ≤ W.card + 2 := by
        rw [hW2]
        have h1 := Finset.card_union_le (W.erase (n + k))
          ((gateAt C k).inputs.filter (fun i => i < n + k)).toFinset
        have h2 : ((gateAt C k).inputs.filter (fun i => i < n + k)).toFinset.card ≤ 2 :=
          (List.toFinset_card_le _).trans
            ((List.length_filter_le _ _).trans (hR k (by omega)))
        have h3 := Finset.card_erase_of_mem hmem
        have h4 : 0 < W.card := Finset.card_pos.2 ⟨_, hmem⟩
        omega
      obtain ⟨T, hT, hdep⟩ := ih (by omega) W2 hlt2
      refine ⟨T, by omega, ?_⟩
      intro x y h w hw
      by_cases hwk : w = n + k
      · rw [hwk, val_gate (by simp) (by omega), val_gate (by simp) (by omega)]
        congr 1
        apply List.map_congr_left
        intro i hi
        by_cases hlt : i < n + k
        · simp only [ite_eq_left hlt]
          exact hdep x y h i (hs2 i hi hlt)
        · simp only [ite_eq_right hlt]
      · exact hdep x y h w (hs1 w hw hwk)
    · obtain ⟨T, hT, hdep⟩ := ih (by omega) W (by
        intro w hw
        have h1 := hW w hw
        have h2 : w ≠ n + k := fun h => hmem (h ▸ hw)
        omega)
      exact ⟨T, by omega, hdep⟩

lemma main (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h2 : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hF : PEqualNP.MetaComplexity.circuitFun n C = graphFun G ∅) :
    G.support.ncard ≤ C.size + 1 := by
  obtain ⟨T, hT, hdep⟩ : ∃ T : Finset (Fin n), T.card ≤ C.gates.length + 1 ∧
      ∀ x y : Fin n → Bool, (∀ i ∈ T, x i = y i) →
        val C (List.ofFn x) C.output = val C (List.ofFn y) C.output := by
    by_cases ho : C.output < n + C.gates.length
    · obtain ⟨T, hT, hdep⟩ := dep n C (fun j hj => h2 _ (gateAt_mem hj)) C.gates.length le_rfl
        {C.output} (by simpa using ho)
      exact ⟨T, by simpa using hT, fun x y h => hdep x y h _ (by simp)⟩
    · exact ⟨∅, by simp, fun x y _ => by
        rw [val_ge (n := n) (by simp) (by omega), val_ge (n := n) (by simp) (by omega)]⟩
  have hsub : G.support ⊆ (T : Set (Fin n)) := by
    intro v hv
    obtain ⟨u, huv⟩ := (SimpleGraph.mem_support G).1 hv
    by_contra hvT
    have e := hdep (fun w => decide (w = u ∨ w = v)) (fun w => decide (w = u)) (by
      intro i hi
      have hne : i ≠ v := fun h => hvT (h ▸ hi)
      simp [hne])
    have fx : val C (List.ofFn (fun w => decide (w = u ∨ w = v))) C.output =
        graphFun G ∅ (fun w => decide (w = u ∨ w = v)) :=
      congrFun hF (fun w => decide (w = u ∨ w = v))
    have fy : val C (List.ofFn (fun w => decide (w = u))) C.output =
        graphFun G ∅ (fun w => decide (w = u)) :=
      congrFun hF (fun w => decide (w = u))
    have t1 : graphFun G ∅ (fun w => decide (w = u ∨ w = v)) = true := by
      unfold graphFun
      rw [Bool.or_eq_true]
      right
      rw [decide_eq_true_iff]
      exact ⟨v, u, huv, by simp, by simp⟩
    have t2 : graphFun G ∅ (fun w => decide (w = u)) = false := by
      unfold graphFun
      rw [Bool.or_eq_false_iff]
      refine ⟨by simp, ?_⟩
      rw [decide_eq_false_iff_not]
      rintro ⟨a, b, hab, ha, hb⟩
      have ha' : a = u := by simpa using ha
      have hb' : b = u := by simpa using hb
      exact hab.ne (ha'.trans hb'.symm)
    rw [fx, fy, t1, t2] at e
    cases e
  calc G.support.ncard ≤ (T : Set (Fin n)).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet T)
    _ = T.card := Set.ncard_coe_finset T
    _ ≤ C.size + 1 := hT

end PEqualNP.Outside.L_meta_2448_aux.inputBound

namespace PEqualNP.Outside.L_meta_2448_aux.twoSilentProducts

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

def Cross {n : ℕ} (L R : Finset (Fin n)) (u v : Fin n) : Prop :=
  (u ∈ L ∧ v ∈ R) ∨ (v ∈ L ∧ u ∈ R)

lemma cross_mem {n : ℕ} {L R : Finset (Fin n)} {u v : Fin n}
    (h : Cross L R u v) : u ∈ L ∪ R ∧ v ∈ L ∪ R := by
  unfold Cross at h
  simp only [Finset.mem_union]
  tauto

lemma star_forest_cover_budget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (K : Finset (Fin n))
    (hc : ∀ u v, G.Adj u v → u ∈ K ∨ v ∈ K)
    (hi : ∀ u ∈ K, ∀ v ∈ K, ¬ G.Adj u v)
    (hl : ∀ u, u ∉ K → ∀ v w, G.Adj u v → G.Adj u w → v = w)
    (ha : ∀ u ∈ K, u ∈ G.support) :
    G.edgeFinset.card + K.card ≤ G.support.ncard := by
  classical
  have hex : ∀ e ∈ G.edgeFinset, ∃ u, ∃ v,
      u ∉ K ∧ v ∈ K ∧ G.Adj u v ∧ e = s(u, v) := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
      have huv : G.Adj u v := SimpleGraph.mem_edgeFinset.mp he
      rcases hc u v huv with hu | hv
      · exact ⟨v, u, fun hv => hi u hu v hv huv, hu, huv.symm, Sym2.eq_swap⟩
      · exact ⟨u, v, fun hu => hi u hu v hv huv, hv, huv, rfl⟩
  let leaf : {e // e ∈ G.edgeFinset} → Fin n := fun e => (hex e.val e.property).choose
  have hp : ∀ e : {e // e ∈ G.edgeFinset}, ∃ v,
      leaf e ∉ K ∧ v ∈ K ∧ G.Adj (leaf e) v ∧ e.val = s(leaf e, v) := by
    intro e
    exact (hex e.val e.property).choose_spec
  have hinj : Set.InjOn leaf (G.edgeFinset.attach : Set {e // e ∈ G.edgeFinset}) := by
    intro e1 _ e2 _ he
    obtain ⟨v1, h1, _, ha1, hv1⟩ := hp e1
    obtain ⟨v2, _, _, ha2, hv2⟩ := hp e2
    have hv : v1 = v2 := hl (leaf e1) h1 v1 v2 ha1 (he ▸ ha2)
    apply Subtype.ext
    rw [hv1, hv2, he, hv]
  let L := G.edgeFinset.attach.image leaf
  have hcard : L.card = G.edgeFinset.card := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_attach]
  have hd : Disjoint K L := by
    apply Finset.disjoint_left.mpr
    intro u hu hL
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hL
    exact (hp e).choose_spec.1 hu
  have hs : ((K ∪ L : Finset (Fin n)) : Set (Fin n)) ⊆ G.support := by
    intro u hu
    rcases Finset.mem_union.mp hu with huK | huL
    · exact ha u huK
    · obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp huL
      obtain ⟨v, _, _, huv, _⟩ := hp e
      exact huv.mem_support_left
  have hn := Set.ncard_le_ncard hs (Set.toFinite G.support)
  rw [Set.ncard_coe_finset, Finset.card_union_of_disjoint hd, hcard] at hn
  omega

lemma biclique_cover {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (L R : Finset (Fin n))
    (hedge : ∀ u ∈ L, ∀ v ∈ R, G.Adj u v) :
    ∃ K : Finset (Fin n), K ⊆ L ∪ R ∧ K.card ≤ 1 ∧
      (∀ u ∈ K, u ∈ G.support) ∧
      ∀ u v, Cross L R u v → u ∈ K ∨ v ∈ K := by
  classical
  by_cases hL : L.Nonempty
  · by_cases hR : R.Nonempty
    · have hsmall : L.card ≤ 1 ∨ R.card ≤ 1 := by
        by_contra! h
        obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h.1
        have hs : R ⊆ Finset.univ.filter (fun w => G.Adj u w ∧ G.Adj v w) := by
          intro w hw
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hedge u hu w hw, hedge v hv w hw⟩
        have hcard := Finset.card_le_card hs
        have hfour := h4 u v huv
        omega
      rcases hsmall with hsmall | hsmall
      · obtain ⟨u, hLu⟩ := Finset.card_eq_one.mp (le_antisymm hsmall (Finset.card_pos.mpr hL))
        obtain ⟨v, hv⟩ := hR
        refine ⟨{u}, ?_, by simp, ?_, ?_⟩
        · intro w hw
          rw [Finset.mem_singleton] at hw
          subst w
          apply Finset.mem_union_left
          rw [hLu]
          simp
        · intro w hw
          rw [Finset.mem_singleton] at hw
          subst w
          exact (hedge u (by rw [hLu]; simp) v hv).mem_support_left
        · intro a b hab
          simp only [Cross, hLu, Finset.mem_singleton] at hab ⊢
          tauto
      · obtain ⟨v, hRv⟩ := Finset.card_eq_one.mp (le_antisymm hsmall (Finset.card_pos.mpr hR))
        obtain ⟨u, hu⟩ := hL
        refine ⟨{v}, ?_, by simp, ?_, ?_⟩
        · intro w hw
          rw [Finset.mem_singleton] at hw
          subst w
          apply Finset.mem_union_right
          rw [hRv]
          simp
        · intro w hw
          rw [Finset.mem_singleton] at hw
          subst w
          exact (hedge u hu v (by rw [hRv]; simp)).mem_support_right
        · intro a b hab
          simp only [Cross, hRv, Finset.mem_singleton] at hab ⊢
          tauto
    · refine ⟨∅, by simp, by simp, by simp, ?_⟩
      have he : R = ∅ := Finset.not_nonempty_iff_eq_empty.mp hR
      simp [Cross, he]
  · refine ⟨∅, by simp, by simp, by simp, ?_⟩
    have he : L = ∅ := Finset.not_nonempty_iff_eq_empty.mp hL
    simp [Cross, he]

lemma two_disjoint_bicliques_budget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (A B C D : Finset (Fin n))
    (hd : Disjoint (A ∪ B) (C ∪ D))
    (hedge : ∀ u v, G.Adj u v ↔ Cross A B u v ∨ Cross C D u v) :
    ∃ K : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ K ∨ v ∈ K) ∧
      G.edgeFinset.card + K.card ≤ G.support.ncard := by
  classical
  obtain ⟨K1, hs1, hc1, ha1, he1⟩ := biclique_cover G h4 A B
    (fun u hu v hv => (hedge u v).mpr (Or.inl (Or.inl ⟨hu, hv⟩)))
  obtain ⟨K2, hs2, hc2, ha2, he2⟩ := biclique_cover G h4 C D
    (fun u hu v hv => (hedge u v).mpr (Or.inr (Or.inl ⟨hu, hv⟩)))
  have sep : ∀ u, u ∈ A ∪ B → u ∈ C ∪ D → False := Finset.disjoint_left.mp hd
  have k1 (u : Fin n) (hu : u ∈ A ∪ B) (hk : u ∈ K1 ∪ K2) : u ∈ K1 := by
    rcases Finset.mem_union.mp hk with hk | hk
    · exact hk
    · exact (sep u hu (hs2 hk)).elim
  have k2 (u : Fin n) (hu : u ∈ C ∪ D) (hk : u ∈ K1 ∪ K2) : u ∈ K2 := by
    rcases Finset.mem_union.mp hk with hk | hk
    · exact (sep u (hs1 hk) hu).elim
    · exact hk
  have hcov : ∀ u v, G.Adj u v → u ∈ K1 ∪ K2 ∨ v ∈ K1 ∪ K2 := by
    intro u v huv
    rcases (hedge u v).mp huv with h | h
    · rcases he1 u v h with h | h
      · exact Or.inl (Finset.mem_union_left _ h)
      · exact Or.inr (Finset.mem_union_left _ h)
    · rcases he2 u v h with h | h
      · exact Or.inl (Finset.mem_union_right _ h)
      · exact Or.inr (Finset.mem_union_right _ h)
  refine ⟨K1 ∪ K2, hcov, star_forest_cover_budget G (K1 ∪ K2) hcov ?_ ?_ ?_⟩
  · intro u hu v hv huv
    have heq : u = v := by
      rcases (hedge u v).mp huv with h | h
      · exact Finset.card_le_one.mp hc1 u (k1 u (cross_mem h).1 hu) v (k1 v (cross_mem h).2 hv)
      · exact Finset.card_le_one.mp hc2 u (k2 u (cross_mem h).1 hu) v (k2 v (cross_mem h).2 hv)
    exact huv.ne heq
  · intro u hu v w huv huw
    have hv : v ∈ K1 ∪ K2 := (hcov u v huv).resolve_left hu
    have hw : w ∈ K1 ∪ K2 := (hcov u w huw).resolve_left hu
    rcases (hedge u v).mp huv with h1 | h1
    · rcases (hedge u w).mp huw with h2 | h2
      · exact Finset.card_le_one.mp hc1 v (k1 v (cross_mem h1).2 hv) w (k1 w (cross_mem h2).2 hw)
      · exact (sep u (cross_mem h1).1 (cross_mem h2).1).elim
    · rcases (hedge u w).mp huw with h2 | h2
      · exact (sep u (cross_mem h2).1 (cross_mem h1).1).elim
      · exact Finset.card_le_one.mp hc2 v (k2 v (cross_mem h1).2 hv) w (k2 w (cross_mem h2).2 hw)
  · intro u hu
    rcases Finset.mem_union.mp hu with h | h
    · exact ha1 u h
    · exact ha2 u h

set_option maxHeartbeats 4000000 in
lemma four_sides_budget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (P Q R S : Finset (Fin n))
    (hPQ : Disjoint P Q) (hRS : Disjoint R S)
    (hedge : ∀ u v, G.Adj u v ↔
      (u ∈ P ∨ v ∈ P) ∧ (u ∈ Q ∨ v ∈ Q) ∧ (u ∈ R ∨ v ∈ R) ∧ (u ∈ S ∨ v ∈ S)) :
    ∃ K : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ K ∨ v ∈ K) ∧
      G.edgeFinset.card + K.card ≤ G.support.ncard := by
  have hpq : ∀ u, u ∈ P → u ∈ Q → False := Finset.disjoint_left.mp hPQ
  have hrs : ∀ u, u ∈ R → u ∈ S → False := Finset.disjoint_left.mp hRS
  apply two_disjoint_bicliques_budget G h4 (P ∩ R) (Q ∩ S) (P ∩ S) (Q ∩ R)
  · apply Finset.disjoint_left.mpr
    intro u h1 h2
    simp only [Finset.mem_union, Finset.mem_inter] at h1 h2
    have hPQu := hpq u
    have hRSu := hrs u
    tauto
  · intro u v
    rw [hedge]
    simp only [Cross, Finset.mem_inter]
    have hPQu := hpq u
    have hPQv := hpq v
    have hRSu := hrs u
    have hRSv := hrs v
    tauto

lemma exists_minimum_star_of_four_sides {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (P Q R S : Finset (Fin n))
    (hPQ : Disjoint P Q) (hRS : Disjoint R S)
    (hedge : ∀ u v, G.Adj u v ↔
      (u ∈ P ∨ v ∈ P) ∧ (u ∈ Q ∨ v ∈ Q) ∧ (u ∈ R ∨ v ∈ R) ∧ (u ∈ S ∨ v ∈ S)) :
    ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧
      (∀ E : Circuit, Monotone2 E → circuitFun n E = graphFun G ∅ → D.size ≤ E.size) ∧
      HasStarProfile n G D := by
  classical
  obtain ⟨K, hK, hbudget⟩ := four_sides_budget G h4 P Q R S hPQ hRS hedge
  by_cases hE : G.edgeFinset.Nonempty
  · have hcover : ∀ e ∈ G.edgeFinset, ∃ u ∈ K, u ∈ e := by
      intro e he
      induction e using Sym2.ind with
      | _ u v =>
        rcases hK u v (SimpleGraph.mem_edgeFinset.mp he) with hu | hv
        · exact ⟨u, hu, Sym2.mem_mk_left _ _⟩
        · exact ⟨v, hv, Sym2.mem_mk_right _ _⟩
    obtain ⟨D, hD, hDf, hDs, hDsize⟩ :=
      PEqualNP.Outside.L_meta_2448.StarCoverPrototype.star_cover_witness G hE K hcover
    refine ⟨D, hD, hDf, ?_, hDs⟩
    intro E hmono hEf
    have hsupport := PEqualNP.Outside.L_meta_2448_aux.inputBound.main n G E
      (fun g hg => (hmono g hg).2) hEf
    omega
  · exact PEqualNP.Outside.L_meta_2448_aux.oneJunkStar.empty_graph_star_minimum G
      (Finset.not_nonempty_iff_eq_empty.mp hE)

end PEqualNP.Outside.L_meta_2448_aux.twoSilentProducts
