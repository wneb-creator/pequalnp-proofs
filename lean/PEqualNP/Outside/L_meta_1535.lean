import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1535

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_append (A B : List Gate) (x : List Bool) : run (A ++ B) x = run B (run A x) := by
  simp [run, List.foldl_append]

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

lemma gate_value' {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (k : ℕ) (hk : k < gs.length) :
    value ⟨gs, 0⟩ x (n + k) =
      gs[k].op.eval (gs[k].inputs.map fun r => if r < n + k then value ⟨gs, 0⟩ x r else false) := by
  have h := gate_value ⟨gs, 0⟩ x (n + k) (by omega) (by change n + k < n + gs.length; omega)
  simpa only [Nat.add_sub_cancel_left] using h

def V {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (w : ℕ) : Bool := value ⟨gs, 0⟩ x w

lemma V_gate {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (k : ℕ) (hk : k < gs.length) :
    V gs x (n + k) =
      gs[k].op.eval (gs[k].inputs.map fun r => if r < n + k then V gs x r else false) :=
  gate_value' gs x k hk

lemma V_missing {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (w : ℕ)
    (hw : n + gs.length ≤ w) : V gs x w = false :=
  missing_value ⟨gs, 0⟩ x w hw

lemma V_input {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    V gs x w = x ⟨w, hw⟩ := by
  change (run gs (List.ofFn x)).getD w false = x ⟨w, hw⟩
  have hp : w < (List.ofFn x).length := by simpa using hw
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma three_distinct (l : List ℕ) (a b c : ℕ) (hl : l.length ≤ 2) (ha : a ∈ l) (hb : b ∈ l)
    (hc : c ∈ l) : a = b ∨ b = c ∨ a = c := by
  rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, t⟩⟩⟩
  · simp at ha
  · simp at ha hb hc; omega
  · simp at ha hb hc; omega
  · simp at hl

lemma mono {n : ℕ} (gs : List Gate) (hops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true) :
    ∀ w, V gs x w = true → V gs y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · rw [V_input gs x w hn, V_input gs y w hn]
      exact hxy _
    by_cases hw : n + gs.length ≤ w
    · rw [V_missing gs x w hw]
      intro hh
      exact Bool.noConfusion hh
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : k < gs.length := by omega
    rw [V_gate gs x k hk, V_gate gs y k hk]
    have hr (r : ℕ) : (if r < n + k then V gs x r else false) = true →
        (if r < n + k then V gs y r else false) = true := by
      by_cases h' : r < n + k
      · simpa [h'] using ih r h'
      · simp [h']
    rcases hops gs[k] (List.getElem_mem hk) with hop | hop
    · simp only [hop, GateOp.eval, List.all_eq_true, id_eq]
      intro hx b hb
      obtain ⟨r, hm, rfl⟩ := List.mem_map.mp hb
      exact hr r (hx _ (List.mem_map.mpr ⟨r, hm, rfl⟩))
    · simp only [hop, GateOp.eval, List.any_eq_true, id_eq]
      intro hx
      obtain ⟨b, hb, hv⟩ := hx
      obtain ⟨r, hm, rfl⟩ := List.mem_map.mp hb
      exact ⟨_, List.mem_map.mpr ⟨r, hm, rfl⟩, hr r hv⟩


def e {n : ℕ} (u : Fin n) : Fin n → Bool := fun uk => decide (uk = u)

def z {n : ℕ} (y : Fin n → Bool) (u : Fin n) : Fin n → Bool := fun v => y v || decide (v = u)

def InK {n : ℕ} (gs : List Gate) (S0 : Finset (Fin n)) (o : ℕ) (bk : ℕ) : Prop :=
  ∀ bK : Set ℕ, (∀ bk0 : ℕ, bk0 < gs.length → o = n + bk0 →
      (∀ bu0 : Fin n, V gs (e bu0) (n + bk0) = true → bu0 ∈ S0) → bk0 ∈ bK) →
    (∀ bk1 ∈ bK, ∀ (bg1 : Gate) (bk2 : ℕ), gs[bk1]? = some bg1 → n + bk2 ∈ bg1.inputs → bk2 < bk1 →
      (∀ bu1 : Fin n, V gs (e bu1) (n + bk2) = true → bu1 ∈ S0) → bk2 ∈ bK) → bk ∈ bK

def Core {n : ℕ} (gs : List Gate) (S0 : Finset (Fin n)) (o : ℕ) (y : Fin n → Bool) : Prop :=
  ∀ bw : ℕ, (∃ (bk : ℕ) (bg : Gate), InK gs S0 o bk ∧ gs[bk]? = some bg ∧ bg.op = GateOp.and ∧
      bw ∈ bg.inputs ∧ bw < n + bk ∧ ¬ (∀ bu2 : Fin n, V gs (e bu2) bw = true → bu2 ∈ S0)) →
    ∃ u4 : Fin n, V gs (e u4) bw = true ∧ y u4 = true

def Good {n : ℕ} (gs : List Gate) (S0 : Finset (Fin n)) (o : ℕ) (y : Fin n → Bool) (r : ℕ) : Prop :=
  V gs y r = false ∧ ((∃ hr : r < n, (⟨r, hr⟩ : Fin n) ∈ S0) ∨
    (∃ j, r = n + j ∧ j < gs.length ∧ InK gs S0 o j))

def Q {n : ℕ} (gs : List Gate) (S0 : Finset (Fin n)) (o : ℕ) (y : Fin n → Bool) (u : Fin n)
    (k : ℕ) : Prop :=
  k < gs.length ∧ InK gs S0 o k ∧ V gs y (n + k) = false ∧ V gs (z y u) (n + k) = true ∧
    ∃ u' ∈ S0, u' < u ∧ V gs (z y u') (n + k) = true

lemma inK_supp {n : ℕ} (gs : List Gate) (S0 : Finset (Fin n)) (o : ℕ) (k : ℕ)
    (hK : InK gs S0 o k) : ∀ u : Fin n, V gs (e u) (n + k) = true → u ∈ S0 :=
  hK {k | ∀ u : Fin n, V gs (e u) (n + k) = true → u ∈ S0} (fun _ _ _ h => h)
    (fun _ _ _ _ _ _ _ h => h)

lemma inK_step {n : ℕ} (gs : List Gate) (S0 : Finset (Fin n)) (o : ℕ) (k1 k2 : ℕ) (g : Gate)
    (hK : InK gs S0 o k1) (hg : gs[k1]? = some g) (hin : n + k2 ∈ g.inputs) (hlt : k2 < k1)
    (hs : ∀ u : Fin n, V gs (e u) (n + k2) = true → u ∈ S0) : InK gs S0 o k2 :=
  fun bK h1 h2 => h2 k1 (hK bK h1 h2) g k2 hg hin hlt hs

lemma good_of {n : ℕ} (gs : List Gate) (S0 : Finset (Fin n)) (o : ℕ) (y : Fin n → Bool)
    (k : ℕ) (hk : k < gs.length) (hK : InK gs S0 o k) (r : ℕ) (hr : r ∈ gs[k].inputs)
    (hlt : r < n + k) (hyr : V gs y r = false)
    (hsub : ∀ u : Fin n, V gs (e u) r = true → u ∈ S0) : Good gs S0 o y r := by
  refine ⟨hyr, ?_⟩
  by_cases hn : r < n
  · left
    refine ⟨hn, hsub ⟨r, hn⟩ ?_⟩
    rw [V_input gs _ r hn]
    simp [e]
  · right
    obtain ⟨j, rfl⟩ : ∃ j, r = n + j := ⟨r - n, by omega⟩
    exact ⟨j, rfl, by omega,
      inK_step gs S0 o k j gs[k] hK (List.getElem?_eq_getElem hk) hr (by omega) hsub⟩

lemma src {n : ℕ} (gs : List Gate) (hops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (S0 : Finset (Fin n)) (o : ℕ) (y : Fin n → Bool) (hcore : Core gs S0 o y)
    (k : ℕ) (hk : k < gs.length) (hK : InK gs S0 o k) (hy : V gs y (n + k) = false) :
    (∀ x : Fin n → Bool, V gs x (n + k) = false) ∨
    (∃ r, r < n + k ∧ Good gs S0 o y r ∧
      ∀ x : Fin n → Bool, V gs x (n + k) = true → V gs x r = true) ∨
    ((∀ r ∈ gs[k].inputs, r < n + k → Good gs S0 o y r) ∧
      ∀ x : Fin n → Bool, V gs x (n + k) = true →
        ∃ r ∈ gs[k].inputs, r < n + k ∧ V gs x r = true) := by
  have hsupp := inK_supp gs S0 o k hK
  rcases hops gs[k] (List.getElem_mem hk) with hop | hop
  · by_cases hex : ∃ r ∈ gs[k].inputs, (if r < n + k then V gs y r else false) = false
    · obtain ⟨r, hr, hf⟩ := hex
      have hall : ∀ x : Fin n → Bool, V gs x (n + k) = true →
          (if r < n + k then V gs x r else false) = true := by
        intro x hx
        rw [V_gate gs x k hk, hop] at hx
        simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hx
        exact hx _ ⟨r, hr, rfl⟩
      by_cases hlt : r < n + k
      · have hyr : V gs y r = false := by simpa [hlt] using hf
        refine Or.inr (Or.inl ⟨r, hlt, ?_, fun x hx => by simpa [hlt] using hall x hx⟩)
        apply good_of gs S0 o y k hk hK r hr hlt hyr
        by_contra hns
        obtain ⟨u4, h1, h2⟩ :=
          hcore r ⟨k, gs[k], hK, List.getElem?_eq_getElem hk, hop, hr, hlt, hns⟩
        have hm := mono gs hops (e u4) y (by
          intro p hp
          have hp' : p = u4 := by simpa [e] using hp
          rw [hp']
          exact h2) r h1
        rw [hyr] at hm
        exact Bool.noConfusion hm
      · refine Or.inl fun x => ?_
        by_contra hne
        have hx : V gs x (n + k) = true := by simpa using hne
        have := hall x hx
        simp [hlt] at this
    · exfalso
      rw [V_gate gs y k hk, hop] at hy
      have hall : (gs[k].inputs.map fun r => if r < n + k then V gs y r else false).all id
          = true := by
        simp only [List.all_eq_true, List.mem_map, id_eq]
        rintro b ⟨r, hr, rfl⟩
        by_contra hb
        exact hex ⟨r, hr, by simpa using hb⟩
      simp only [GateOp.eval] at hy
      rw [hall] at hy
      exact Bool.noConfusion hy
  · have hin : ∀ r ∈ gs[k].inputs, r < n + k → ∀ x : Fin n → Bool, V gs x r = true →
        V gs x (n + k) = true := by
      intro r hr hlt x hx
      rw [V_gate gs x k hk, hop]
      simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
      exact ⟨_, ⟨r, hr, rfl⟩, by simp [hlt, hx]⟩
    refine Or.inr (Or.inr ⟨fun r hr hlt => ?_, fun x hx => ?_⟩)
    · apply good_of gs S0 o y k hk hK r hr hlt ?_ (fun u hu => hsupp u (hin r hr hlt _ hu))
      by_contra hb
      have hb' : V gs y r = true := by simpa using hb
      have := hin r hr hlt y hb'
      rw [hy] at this
      exact Bool.noConfusion this
    · rw [V_gate gs x k hk, hop] at hx
      simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hx
      obtain ⟨b, ⟨r, hr, rfl⟩, hb⟩ := hx
      by_cases hlt : r < n + k
      · exact ⟨r, hr, hlt, by simpa [hlt] using hb⟩
      · simp [hlt] at hb

lemma good_min {n : ℕ} (gs : List Gate) (S0 : Finset (Fin n)) (o : ℕ) (y : Fin n → Bool)
    (hy0 : ∀ u ∈ S0, y u = false) (r k : ℕ) (u : Fin n) (hg : Good gs S0 o y r)
    (hlt : r < n + k) (hmin : ∀ j < k, ¬ Q gs S0 o y u j) (h1 : V gs (z y u) r = true)
    (u' : Fin n) (hu' : u' ∈ S0) (hlt' : u' < u) (h2 : V gs (z y u') r = true) : False := by
  obtain ⟨hyr, ⟨hr, hS⟩ | ⟨j, rfl, hj, hK⟩⟩ := hg
  · rw [V_input gs _ r hr] at h1 h2
    have hy := hy0 _ hS
    simp only [z, hy, Bool.false_or, decide_eq_true_eq] at h1 h2
    rw [← h1, ← h2] at hlt'
    exact lt_irrefl _ hlt'
  · exact hmin j (by omega) ⟨hj, hK, hyr, h1, u', hu', hlt', h2⟩

lemma row_inj {n : ℕ} (gs : List Gate) (hops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (S0 : Finset (Fin n)) (o : ℕ) (y : Fin n → Bool) (hcore : Core gs S0 o y)
    (hy0 : ∀ u ∈ S0, y u = false) (k : ℕ) (p r : Fin n)
    (hQp : Q gs S0 o y p k) (hminp : ∀ j < k, ¬ Q gs S0 o y p j)
    (hQr : Q gs S0 o y r k) (hminr : ∀ j < k, ¬ Q gs S0 o y r j)
    (hr : r ∈ S0) (hrp : r < p) : False := by
  obtain ⟨hk, hK, hyk, h2, p', hp', hlt, h3⟩ := hQp
  obtain ⟨_, _, _, g2, r', hr', hlt', g3⟩ := hQr
  rcases src gs hops S0 o y hcore k hk hK hyk with h | ⟨r0, hl0, hg0, hx⟩ | ⟨hgood, hsrc⟩
  · rw [h] at h2
    exact Bool.noConfusion h2
  · exact good_min gs S0 o y hy0 r0 k p hg0 hl0 hminp (hx _ h2) r hr hrp (hx _ g2)
  · obtain ⟨r1, hr1, hl1, hv1⟩ := hsrc _ h2
    obtain ⟨r2, hr2, hl2, hv2⟩ := hsrc _ g2
    obtain ⟨r3, hr3, hl3, hv3⟩ := hsrc _ g3
    rcases three_distinct _ r1 r2 r3 (hlen _ (List.getElem_mem hk)) hr1 hr2 hr3 with e1 | e1 | e1
    · subst e1
      exact good_min gs S0 o y hy0 r1 k p (hgood r1 hr1 hl1) hl1 hminp hv1 r hr hrp hv2
    · subst e1
      exact good_min gs S0 o y hy0 r2 k r (hgood r2 hr2 hl2) hl2 hminr hv2 r' hr' hlt' hv3
    · subst e1
      exact good_min gs S0 o y hy0 r1 k p (hgood r1 hr1 hl1) hl1 hminp hv1 r' hr'
        (lt_trans hlt' hrp) hv3

lemma cross {n : ℕ} (gs : List Gate)
    (hnorm : ∀ ak : ℕ, ak < gs.length →
      (Finset.univ.filter (fun au : Fin n => V gs (e au) (n + ak) = true)).card ≤ 1 →
      ∀ ax : Fin n → Bool, V gs ax (n + ak) =
        decide (∃ av : Fin n, V gs (e av) (n + ak) = true ∧ ax av = true))
    (S0 S1 : Finset (Fin n)) (o : ℕ) (y : Fin n → Bool)
    (hy0 : ∀ u ∈ S0, y u = false) (k : ℕ) (p : Fin n) (hQ : Q gs S0 o y p k)
    (hsub1 : ∀ u : Fin n, V gs (e u) (n + k) = true → u ∈ S1)
    (hinter : (S0 ∩ S1).card ≤ 1) : False := by
  obtain ⟨hk, hK, hyk, h2, p', hp', hlt, h3⟩ := hQ
  have hsupp := inK_supp gs S0 o k hK
  have hc : (Finset.univ.filter (fun au : Fin n => V gs (e au) (n + k) = true)).card ≤ 1 := by
    refine le_trans (Finset.card_le_card ?_) hinter
    intro u hu
    have hu' : V gs (e u) (n + k) = true := (Finset.mem_filter.mp hu).2
    exact Finset.mem_inter.mpr ⟨hsupp u hu', hsub1 u hu'⟩
  have N := hnorm k hk hc
  rw [N] at h2 h3
  simp only [decide_eq_true_eq] at h2 h3
  obtain ⟨a1, ha1, hz1⟩ := h2
  obtain ⟨a2, ha2, hz2⟩ := h3
  have y1 := hy0 _ (hsupp a1 ha1)
  have y2 := hy0 _ (hsupp a2 ha2)
  simp only [z, y1, Bool.false_or, decide_eq_true_eq] at hz1
  simp only [z, y2, Bool.false_or, decide_eq_true_eq] at hz2
  have h12 := Finset.card_le_one.mp hc a1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha1⟩)
    a2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha2⟩)
  rw [hz1, hz2] at h12
  rw [h12] at hlt
  exact lt_irrefl _ hlt

lemma main (n m : ℕ) (S : Fin m → Finset (Fin n)) (gs : List Gate) (out : Fin m → ℕ)
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hnorm : ∀ ak : ℕ, ak < gs.length →
      (Finset.univ.filter (fun au : Fin n => V gs (e au) (n + ak) = true)).card ≤ 1 →
      ∀ ax : Fin n → Bool, V gs ax (n + ak) =
        decide (∃ av : Fin n, V gs (e av) (n + ak) = true ∧ ax av = true))
    (hout : ∀ (w : Fin m) (u : Fin n), V gs (e u) (out w) = true ↔ u ∈ S w)
    (h5 : ∀ w0 : Fin m, ∃ y : Fin n → Bool, (∀ u3 ∈ S w0, y u3 = false) ∧
      V gs y (out w0) = false ∧ Core gs (S w0) (out w0) y) :
    ∑ w1 : Fin m, (S w1).card ≤
      gs.length + (Finset.univ.filter (fun w5 : Fin m => (S w5).Nonempty)).card := by
  classical
  choose y hy0 hyo hcore using h5
  have hops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or := fun g h => (hg g h).1
  have hlen : ∀ g ∈ gs, g.inputs.length ≤ 2 := fun g h => (hg g h).2
  let A : Fin m → Finset (Fin n) := fun w => (S w).filter (fun u => ∃ u' ∈ S w, u' < u)
  have hA : ∀ w, (S w).card ≤ (A w).card + (if (S w).Nonempty then 1 else 0) := by
    intro w
    by_cases hne : (S w).Nonempty
    · have hsub : (S w).erase ((S w).min' hne) ⊆ A w := by
        intro u hu
        refine Finset.mem_filter.mpr ⟨Finset.mem_of_mem_erase hu, (S w).min' hne,
          Finset.min'_mem _ hne, ?_⟩
        exact lt_of_le_of_ne (Finset.min'_le _ u (Finset.mem_of_mem_erase hu))
          (Ne.symm (Finset.ne_of_mem_erase hu))
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem (Finset.min'_mem _ hne)] at h1
      rw [ite_eq_left hne]
      omega
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      simp [hne]
  have hE : ∀ w, ∀ u ∈ A w, ∃ k, Q gs (S w) (out w) (y w) u k := by
    intro w u hu
    obtain ⟨huS, u', hu', hlt⟩ := Finset.mem_filter.mp hu
    have t1 : V gs (e u) (out w) = true := (hout w u).mpr huS
    have t2 : V gs (e u') (out w) = true := (hout w u').mpr hu'
    have t0 := hyo w
    by_cases hn : out w < n
    · exfalso
      rw [V_input gs _ _ hn] at t1 t2
      have a1 : (⟨out w, hn⟩ : Fin n) = u := by simpa [e] using t1
      have a2 : (⟨out w, hn⟩ : Fin n) = u' := by simpa [e] using t2
      rw [← a1, ← a2] at hlt
      exact lt_irrefl _ hlt
    by_cases hw : n + gs.length ≤ out w
    · exfalso
      rw [V_missing gs _ _ hw] at t1
      exact Bool.noConfusion t1
    obtain ⟨k0, hk0⟩ : ∃ k, out w = n + k := ⟨out w - n, by omega⟩
    have hmono : ∀ v : Fin n, v ∈ S w → V gs (z (y w) v) (n + k0) = true := by
      intro v hv
      have tv : V gs (e v) (out w) = true := (hout w v).mpr hv
      rw [hk0] at tv
      refine mono gs hops (e v) (z (y w) v) ?_ _ tv
      intro p hp
      have hp' : p = v := by simpa [e] using hp
      simp [z, hp']
    rw [hk0] at t0
    refine ⟨k0, by omega, ?_, t0, hmono u huS, u', hu', hlt, hmono u' hu'⟩
    intro bK h1 _
    refine h1 k0 (by omega) hk0 (fun v hv => (hout w v).mp ?_)
    rw [hk0]
    exact hv
  let F : Fin m → Fin n → ℕ := fun w u =>
    if h : ∃ k, Q gs (S w) (out w) (y w) u k then Nat.find h else 0
  have hF : ∀ w, ∀ u ∈ A w, Q gs (S w) (out w) (y w) u (F w u) ∧
      ∀ j < F w u, ¬ Q gs (S w) (out w) (y w) u j := by
    intro w u hu
    have h := hE w u hu
    have e1 : F w u = Nat.find h := by simp only [F, h, ↓reduceDIte]
    rw [e1]
    exact ⟨Nat.find_spec h, fun r hr => Nat.find_min h hr⟩
  have hcard : (Finset.univ.sigma A).card ≤ (Finset.range gs.length).card := by
    apply Finset.card_le_card_of_injOn (fun p => F p.1 p.2)
    · intro p hp
      have hp' := (Finset.mem_sigma.mp (Finset.mem_coe.mp hp)).2
      exact Finset.mem_coe.mpr (Finset.mem_range.mpr (hF _ _ hp').1.1)
    · rintro ⟨w, u⟩ hp ⟨w', u'⟩ hp' heq
      have hu : u ∈ A w := (Finset.mem_sigma.mp (Finset.mem_coe.mp hp)).2
      have hu' : u' ∈ A w' := (Finset.mem_sigma.mp (Finset.mem_coe.mp hp')).2
      have heq' : F w u = F w' u' := heq
      obtain ⟨q1, m1⟩ := hF w u hu
      obtain ⟨q2, m2⟩ := hF w' u' hu'
      by_cases hw : w = w'
      · subst hw
        have huu : u = u' := by
          by_contra hne
          rw [← heq'] at q2 m2
          rcases lt_or_gt_of_ne hne with hh | hh
          · exact row_inj gs hops hlen (S w) (out w) (y w) (hcore w) (hy0 w) (F w u) u' u
              q2 m2 q1 m1 (Finset.mem_filter.mp hu).1 hh
          · exact row_inj gs hops hlen (S w) (out w) (y w) (hcore w) (hy0 w) (F w u) u u'
              q1 m1 q2 m2 (Finset.mem_filter.mp hu').1 hh
        rw [huu]
      · exfalso
        rw [← heq'] at q2
        exact cross gs hnorm (S w) (S w') (out w) (y w) (hy0 w) (F w u) u q1
          (inK_supp gs (S w') (out w') (F w u) q2.2.1) (hS w w' hw)
  rw [Finset.card_sigma, Finset.card_range] at hcard
  calc ∑ w1 : Fin m, (S w1).card
      ≤ ∑ w1 : Fin m, ((A w1).card + (if (S w1).Nonempty then 1 else 0)) :=
        Finset.sum_le_sum fun w _ => hA w
    _ = ∑ w1 : Fin m, (A w1).card +
          (Finset.univ.filter (fun w5 : Fin m => (S w5).Nonempty)).card := by
        rw [Finset.sum_add_distrib, Finset.card_filter]
    _ ≤ gs.length + (Finset.univ.filter (fun w5 : Fin m => (S w5).Nonempty)).card := by
        omega

end PEqualNP.Outside.L_meta_1535

theorem PEqualNP.Outside.L_meta_1535 : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ ak : ℕ, ak < gates.length → (Finset.univ.filter (fun au : Fin n => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun auk : Fin n => decide (auk = au)))).getD (n + ak) false = true)).card ≤ 1 → ∀ ax : Fin n → Bool, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn ax)).getD (n + ak) false = decide (∃ av : Fin n, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun avk : Fin n => decide (avk = av)))).getD (n + ak) false = true ∧ ax av = true)) → (∀ (w : Fin m) (u : Fin n), (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun uk : Fin n => decide (uk = u)))).getD (out w) false = true ↔ u ∈ S w) → (∀ w0 : Fin m, ∃ y : Fin n → Bool, (∀ u3 ∈ S w0, y u3 = false) ∧ (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn y)).getD (out w0) false = false ∧ ∀ bw : ℕ, (∃ (bk : ℕ) (bg : PEqualNP.CircuitLowerBounds.Gate), (∀ bK : Set ℕ, (∀ bk0 : ℕ, bk0 < gates.length → out w0 = n + bk0 → (∀ bu0 : Fin n, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun bu0k : Fin n => decide (bu0k = bu0)))).getD (n + bk0) false = true → bu0 ∈ S w0) → bk0 ∈ bK) → (∀ bk1 ∈ bK, ∀ (bg1 : PEqualNP.CircuitLowerBounds.Gate) (bk2 : ℕ), gates[bk1]? = some bg1 → n + bk2 ∈ bg1.inputs → bk2 < bk1 → (∀ bu1 : Fin n, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun bu1k : Fin n => decide (bu1k = bu1)))).getD (n + bk2) false = true → bu1 ∈ S w0) → bk2 ∈ bK) → bk ∈ bK) ∧ gates[bk]? = some bg ∧ bg.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ bw ∈ bg.inputs ∧ bw < n + bk ∧ ¬ (∀ bu2 : Fin n, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun bu2k : Fin n => decide (bu2k = bu2)))).getD (bw) false = true → bu2 ∈ S w0)) → ∃ u4 : Fin n, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u4k : Fin n => decide (u4k = u4)))).getD (bw) false = true ∧ y u4 = true) → ∑ w1 : Fin m, (S w1).card ≤ gates.length + (Finset.univ.filter (fun w5 : Fin m => (S w5).Nonempty)).card := by
  intro n m S gates out h1 h2 h3 h4 h5
  exact PEqualNP.Outside.L_meta_1535.main n m S gates out h1 h2 h3 h4 h5
