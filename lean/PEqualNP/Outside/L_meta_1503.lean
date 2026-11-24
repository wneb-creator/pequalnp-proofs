import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1503

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

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

lemma orIn_bridge (n : ℕ) (C : Circuit) (hA : AO n C) (f : ℕ → Finset (Fin n))
    (h0 : ∀ w, w < n → ∀ u : Fin n, u ∈ f w ↔ u.val = w)
    (hor : ∀ k, k < C.gates.length → (gateAt C k).op = GateOp.or →
      ∀ u : Fin n, u ∈ f (n + k) ↔ ∃ w ∈ (gateAt C k).inputs, u ∈ f w)
    (hand : ∀ k, k < C.gates.length → (gateAt C k).op = GateOp.and → f (n + k) = ∅) :
    ∀ w, w < n + C.gates.length → ∀ u : Fin n, u ∈ f w ↔ OrR n C w u.val := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw u
    by_cases h1 : w < n
    · rw [h0 w h1 u]
      constructor
      · intro h; rw [h]; exact Relation.ReflTransGen.refl
      · intro h
        rcases Relation.ReflTransGen.cases_head h with h2 | ⟨c, ⟨k, hk, _⟩, _⟩
        · exact h2.symm
        · omega
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < C.gates.length := by omega
      obtain ⟨hop, a, b, hab, ha, hb⟩ := hA k hk
      have hlt : ∀ c ∈ (gateAt C k).inputs, c < n + k := by
        intro c hc
        rw [hab] at hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        omega
      rcases hop with hop | hop
      · rw [hand k hk hop]
        constructor
        · intro h; simp at h
        · intro h
          rcases Relation.ReflTransGen.cases_head h with h2 | ⟨c, ⟨k', hk', _, hop', _⟩, _⟩
          · have := u.isLt; omega
          · have : k' = k := by omega
            subst this
            rw [hop] at hop'
            exact absurd hop' (by simp)
      · rw [hor k hk hop u]
        constructor
        · rintro ⟨c, hc, hu⟩
          have h3 := (ih c (hlt c hc) (by have := hlt c hc; omega) u).mp hu
          exact Relation.ReflTransGen.head ⟨k, rfl, hk, hop, hc⟩ h3
        · intro h
          rcases Relation.ReflTransGen.cases_head h with h2 | ⟨c, ⟨k', hk', _, _, hc⟩, h3⟩
          · have := u.isLt; omega
          · have : k' = k := by omega
            subst this
            exact ⟨c, hc, (ih c (hlt c hc) (by have := hlt c hc; omega) u).mpr h3⟩

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

end PEqualNP.Outside.L_meta_1503

theorem PEqualNP.Outside.L_meta_1503 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
  G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
  ∀ (g : ℕ), PEqualNP.TopForm.junk G C = {g} → ∀ (a : ℕ), a ∈ PEqualNP.TopForm.centreless G C →
    ∃ b : Fin 2, PEqualNP.TopForm.opnd C a b = n + g ∧
      (PEqualNP.TopForm.side (n := n) C a (1 - b)).Nonempty ∧
      PEqualNP.TopForm.side (n := n) C a (1 - b) ⊆ PEqualNP.TopForm.wmax G C g ∧
      ∀ v w : Fin n, PEqualNP.EdgeOwnership.gateVal n C a (PEqualNP.EdgeOwnership.pairInput v w) = true →
        PEqualNP.EdgeOwnership.gateVal n C g (PEqualNP.EdgeOwnership.pairInput v w) = true ∧
        (v ∈ PEqualNP.TopForm.side (n := n) C a (1 - b) ∨ w ∈ PEqualNP.TopForm.side (n := n) C a (1 - b)) := by
  intro n G _ C _ hL hT g hj a ha
  exact PEqualNP.Outside.L_meta_1503.final n G C hL hT g hj a ha
