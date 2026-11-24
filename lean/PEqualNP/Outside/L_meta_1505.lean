import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1505

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

end PEqualNP.Outside.L_meta_1505

theorem PEqualNP.Outside.L_meta_1505 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
  PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C →
  PEqualNP.TopForm.TopForm G C → ∀ (g : ℕ), PEqualNP.TopForm.junk G C = {g} →
    (∀ a ∈ PEqualNP.TopForm.tops G C, ∀ b : Fin 2,
      PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C a b) g →
      (PEqualNP.TopForm.side (n := n) C a b).Nonempty →
      ∃ m ∈ PEqualNP.TopForm.mixing G C,
        PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C a b) m ∧
        n + g ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C m).inputs) := by
  intro n G _ C _ _ hL hT g hjunk a ha b hreach hside
  exact PEqualNP.Outside.L_meta_1505.final n G C hL hT g hjunk a ha b hreach hside
