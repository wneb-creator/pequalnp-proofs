import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.LowerPart

namespace PEqualNP.Outside.L_meta_4741_aux

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.MetaComplexity.FoldProg
open PEqualNP.MetaComplexity.LowerPart
open PEqualNP.TopForm
open PEqualNP.CleanedNonEdge
open PEqualNP.SplitCount (unitInput)
open PEqualNP.EdgeOwnership (gateVal pairInput)

variable {n : ℕ}

theorem and_or (o : GateOp) (h1 : o = GateOp.and) (h2 : o = GateOp.or) : False := by
  rw [h1] at h2
  cases h2

theorem fin2_ne' (c : Fin 2) : ¬ (1 - c = c) := by
  revert c; decide

theorem fin2_pick (c : Fin 2) (P : Fin 2 → Prop) (h : P (1 - c)) : P 0 ∨ P 1 := by
  fin_cases c
  · exact Or.inr h
  · exact Or.inl h

theorem col (s : Fin n → Bool) (a b z : Fin n) (h1 : s a ≠ s z) (h2 : s b ≠ s z) : s a = s b := by
  revert h1 h2
  cases s a <;> cases s b <;> cases s z <;> simp

theorem val_and' (C : Circuit) (hC : IsAO2 n C) (k : ℕ) (hk : k < C.gates.length)
    (ho : (gateAt C k).op = GateOp.and) (x : Fin n → Bool) (c : Fin 2) :
    gateVal n C k x = true ↔ wireVal n C (opnd C k c) x = true ∧ wireVal n C (opnd C k (1 - c)) x = true := by
  rw [val_and C hC k hk ho x]
  fin_cases c
  · exact Iff.rfl
  · exact and_comm

theorem val_or' (C : Circuit) (hC : IsAO2 n C) (k : ℕ) (hk : k < C.gates.length)
    (ho : (gateAt C k).op = GateOp.or) (x : Fin n → Bool) (c : Fin 2) :
    gateVal n C k x = true ↔ wireVal n C (opnd C k c) x = true ∨ wireVal n C (opnd C k (1 - c)) x = true := by
  rw [val_or C hC k hk ho x]
  fin_cases c
  · exact Iff.rfl
  · exact or_comm

theorem reach_self (C : Circuit) (hC : IsAO2 n C) (k : ℕ) (hk : k < C.gates.length) : OrReaches n C (n + k) k :=
  (reach_gate C hC k k hk).2 (Or.inl rfl)

theorem reach_trans (C : Circuit) (hC : IsAO2 n C) (k g : ℕ) (_hk : k < C.gates.length)
    (hkg : OrReaches n C (n + k) g) : ∀ w < n + C.gates.length, OrReaches n C w k → OrReaches n C w g := by
  refine wire_induction C hC _ (fun w hw h => absurd h (reach_input C w k hw)) ?_
  intro j hj ih h
  rcases (reach_gate C hC j k hj).1 h with rfl | ⟨ho, c, hc⟩
  · exact hkg
  · exact (reach_gate C hC j g hj).2 (Or.inr ⟨ho, c, ih c hc⟩)

/-- Vertex `z` is a partner variable of the AND `k`. -/
def PZ (C : Circuit) (g k : ℕ) (z : Fin n) : Prop :=
  (OrReaches n C (opnd C k 0) g ∧ wireVal n C (opnd C k 1) (unitInput z) = true) ∨
  (OrReaches n C (opnd C k 1) g ∧ wireVal n C (opnd C k 0) (unitInput z) = true)

theorem pz_iff (C : Circuit) (g k : ℕ) (z : Fin n) : PZ C g k z ↔
    ∃ c, OrReaches n C (opnd C k c) g ∧ wireVal n C (opnd C k (1 - c)) (unitInput z) = true := by
  constructor
  · rintro (h | h)
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  · rintro ⟨c, h⟩
    fin_cases c
    · exact Or.inl h
    · exact Or.inr h

theorem pair_adj (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (y z : Fin n)
    (h : graphFun G ∅ (pairInput y z) = true) : G.Adj y z := by
  obtain ⟨u, w, huw, hu, hw⟩ := (graphFun_empty G _).1 h
  simp only [pairInput, decide_eq_true_eq] at hu hw
  rcases hu with rfl | rfl <;> rcases hw with rfl | rfl
  · exact absurd huw (G.loopless.irrefl _)
  · exact huw
  · exact huw.symm
  · exact absurd huw (G.loopless.irrefl _)

theorem unit_le (y : Fin n) (x : Fin n → Bool) (hy : x y = true) (a : Fin n) (ha : unitInput y a = true) :
    x a = true := by
  simp only [unitInput, decide_eq_true_eq] at ha
  rw [ha]; exact hy

/-- The input `e` restricted to the colour of `v`. -/
def xcol (s : Fin n → Bool) (v : Fin n) (e : Fin n → Bool) : Fin n → Bool :=
  fun y => e y && decide (s y = s v)

theorem xcol_iff (s : Fin n → Bool) (v : Fin n) (e : Fin n → Bool) (a : Fin n) :
    xcol s v e a = true ↔ e a = true ∧ s a = s v := by
  simp [xcol]

/-- The wire has variables of both colours. -/
def Mix (C : Circuit) (s : Fin n → Bool) (v : Fin n) (w : ℕ) : Prop :=
  ∃ y0 y1 : Fin n, wireVal n C w (unitInput y0) = true ∧ wireVal n C w (unitInput y1) = true ∧
    s y0 = s v ∧ s y1 ≠ s v

/-- The wire reaches the cut gate `h` or `g` through ORs. -/
def Dep (n : ℕ) (C : Circuit) (h g w : ℕ) : Prop := OrReaches n C w h ∨ OrReaches n C w g

/-- Gate values of the cut circuit from below, at the input `e`. -/
def uval (n : ℕ) (C : Circuit) (h g : ℕ) (e x' : Fin n → Bool) (k : ℕ) : Bool :=
  if OrReaches n C (n + k) h ∨ OrReaches n C (n + k) g then gateVal n C k x' else gateVal n C k e

theorem uval_pos (C : Circuit) (h g : ℕ) (e x' : Fin n → Bool) (k : ℕ) (hd : Dep n C h g (n + k)) :
    uval n C h g e x' k = gateVal n C k x' := by
  unfold uval
  exact ite_eq_left hd

theorem uval_neg (C : Circuit) (h g : ℕ) (e x' : Fin n → Bool) (k : ℕ) (hd : ¬ Dep n C h g (n + k)) :
    uval n C h g e x' k = gateVal n C k e := by
  unfold uval
  exact ite_eq_right hd

/-- The operands of the cut circuit: operand `c0` of gate `h` is zeroed. -/
def rho (n : ℕ) (C : Circuit) (h : ℕ) (c0 : Fin 2) (k : ℕ) (b : Fin 2) : Src n ℕ :=
  if k = h ∧ b = c0 then none else srcOf n (opnd C k b)

theorem rho_cut (C : Circuit) (h : ℕ) (c0 : Fin 2) : rho n C h c0 h c0 = none := by
  unfold rho
  exact ite_eq_left ⟨rfl, rfl⟩

theorem rho_keep (C : Circuit) (h : ℕ) (c0 : Fin 2) (k : ℕ) (b : Fin 2) (hkb : ¬ (k = h ∧ b = c0)) :
    rho n C h c0 k b = srcOf n (opnd C k b) := by
  unfold rho
  exact ite_eq_right hkb

theorem srcAt_in (e : Fin n → Bool) (t : ℕ → Bool) (w : ℕ) (hw : w < n) :
    srcAt e t (srcOf n w) = e ⟨w, hw⟩ := by
  unfold srcOf
  rw [dite_eq_left hw]
  rfl

theorem srcAt_gate (e : Fin n → Bool) (t : ℕ → Bool) (w : ℕ) (hw : ¬ w < n) :
    srcAt e t (srcOf n w) = t (w - n) := by
  unfold srcOf
  rw [dite_eq_right hw]
  rfl

theorem U_low (C : Circuit) (hC : IsAO2 n C) (h g : ℕ) (e x' : Fin n → Bool)
    (hle : ∀ a, x' a = true → e a = true) (w : ℕ) (hw : w < n + C.gates.length)
    (hwx : wireVal n C w x' = true) : srcAt e (uval n C h g e x') (srcOf n w) = true := by
  have hwe : wireVal n C w e = true := mono C hC x' e hle w hw hwx
  by_cases hwn : w < n
  · rw [srcAt_in e _ w hwn, ← wireVal_lt C w hwn e]
    exact hwe
  · rw [srcAt_gate e _ w hwn]
    have e1 : n + (w - n) = w := by omega
    by_cases hd : Dep n C h g (n + (w - n))
    · rw [uval_pos C h g e x' _ hd]
      show wireVal n C (n + (w - n)) x' = true
      rw [e1]; exact hwx
    · rw [uval_neg C h g e x' _ hd]
      show wireVal n C (n + (w - n)) e = true
      rw [e1]; exact hwe

theorem U_free (C : Circuit) (h g : ℕ) (e x' : Fin n → Bool) (w : ℕ) (hd : ¬ Dep n C h g w)
    (hwe : wireVal n C w e = true) : srcAt e (uval n C h g e x') (srcOf n w) = true := by
  by_cases hwn : w < n
  · rw [srcAt_in e _ w hwn, ← wireVal_lt C w hwn e]
    exact hwe
  · rw [srcAt_gate e _ w hwn]
    have e1 : n + (w - n) = w := by omega
    rw [uval_neg C h g e x' _ (by rw [e1]; exact hd)]
    show wireVal n C (n + (w - n)) e = true
    rw [e1]; exact hwe

section

variable {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {g : ℕ}

theorem and_pair' (H : OneDirty G C g) (k : ℕ) (hk : k < C.gates.length) (ho : (gateAt C k).op = GateOp.and)
    (hkg : k ≠ g) (c : Fin 2) (y z : Fin n) (hy : wireVal n C (opnd C k c) (unitInput y) = true)
    (hz : wireVal n C (opnd C k (1 - c)) (unitInput z) = true) : G.Adj y z := by
  fin_cases c
  · exact and_pair H k hk ho hkg y z hy hz
  · exact (and_pair H k hk ho hkg z y hz hy).symm

theorem not_both' (H : OneDirty G C g) (k : ℕ) (hk : k < C.gates.length) (ho : (gateAt C k).op = GateOp.and)
    (c : Fin 2) (h : OrReaches n C (opnd C k c) g) : ¬ OrReaches n C (opnd C k (1 - c)) g := by
  intro h'
  fin_cases c
  · exact not_both H k hk ho ⟨h, h'⟩
  · exact not_both H k hk ho ⟨h', h⟩

theorem pz_ne (H : OneDirty G C g) (k : ℕ) (z : Fin n) (h : PZ C g k z) : k ≠ g := by
  rintro rfl
  rcases h with ⟨h, _⟩ | ⟨h, _⟩
  · exact not_reach_opnd C H.ao k H.hg 0 h
  · exact not_reach_opnd C H.ao k H.hg 1 h

/-- Where `g` is on and a partner vertex is on, `F` is true. -/
theorem pz_F (H : OneDirty G C g) (k : ℕ) (hk : k < C.gates.length) (ho : (gateAt C k).op = GateOp.and)
    (z : Fin n) (h : PZ C g k z) (x : Fin n → Bool) (hx : gateVal n C g x = true) (hz : x z = true) :
    graphFun G ∅ x = true := by
  obtain ⟨c, hr, hw⟩ := (pz_iff C g k z).1 h
  have hl0 := opnd_lt C H.ao k hk c
  have hl1 := opnd_lt C H.ao k hk (1 - c)
  refine H.others k hk ho (pz_ne H k z h) x ((val_and' C H.ao k hk ho x c).2 ⟨?_, ?_⟩)
  · exact (reach_le C H.ao g _ (by omega) hr).2 x hx
  · exact mono C H.ao _ _ (unit_le z x hz) _ (by omega) hw

/-- A partner vertex in one operand of `g` is adjacent to every variable of the other. -/
theorem pz_opnd (H : OneDirty G C g) (k : ℕ) (hk : k < C.gates.length) (ho : (gateAt C k).op = GateOp.and)
    (z : Fin n) (h : PZ C g k z) (y : Fin n) (c : Fin 2)
    (hzc : wireVal n C (opnd C g c) (unitInput z) = true)
    (hy : wireVal n C (opnd C g (1 - c)) (unitInput y) = true) : G.Adj z y := by
  apply pair_adj
  have hg := H.hg
  have hl0 := opnd_lt C H.ao g hg c
  have hl1 := opnd_lt C H.ao g hg (1 - c)
  refine pz_F H k hk ho z h _ ((val_and' C H.ao g hg H.gand _ c).2 ⟨?_, ?_⟩) (by simp [pairInput])
  · exact mono C H.ao _ _ (unit_le z _ (by simp [pairInput])) _ (by omega) hzc
  · exact mono C H.ao _ _ (unit_le y _ (by simp [pairInput])) _ (by omega) hy

/-- A low gate lies under an operand of an AND, through ORs. -/
theorem above_and (H : OneDirty G C g) : ∀ k < C.gates.length, Low G C (n + k) →
    ∃ T < C.gates.length, (gateAt C T).op = GateOp.and ∧ ∃ c, OrReaches n C (opnd C T c) k := by
  have key : ∀ m, ∀ k < C.gates.length, C.gates.length - k = m → Low G C (n + k) →
      ∃ T < C.gates.length, (gateAt C T).op = GateOp.and ∧ ∃ c, OrReaches n C (opnd C T c) k := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro k hk hm hl
      obtain ⟨o, hol, hoo, hob⟩ := out_gate H
      obtain ⟨_, h | ⟨_, hin⟩⟩ := H.cone k hk
      · have : o = k := by omega
        subst this
        exact absurd hob hl
      · rw [LiveSize.cone_iff] at hin
        obtain ⟨j, ⟨hjl, hkj, hmem⟩, _⟩ := Relation.TransGen.head'_iff.1 hin
        obtain ⟨c, hc⟩ := mem_opnd C H.ao j hjl _ hmem
        rcases LeafBound.ao_op H.ao hjl with ho | ho
        · exact ⟨j, hjl, ho, c, by rw [hc]; exact reach_self C H.ao k hk⟩
        · have hjlow : Low G C (n + j) := fun hb => hl fun x hx =>
            below_or H.ao j hjl ho hb c x (by rw [hc]; exact hx)
          obtain ⟨T, hT, hTo, d, hd⟩ := ih (C.gates.length - j) (by omega) j hjl rfl hjlow
          have hlt := opnd_lt C H.ao T hT d
          refine ⟨T, hT, hTo, d, reach_trans C H.ao j k hjl ?_ _ (by omega) hd⟩
          exact (reach_gate C H.ao j k hjl).2 (Or.inr ⟨ho, c, by rw [hc]; exact reach_self C H.ao k hk⟩)
  exact fun k hk => key _ k hk rfl

/-- Some AND reads `g` through ORs and has a partner vertex. -/
theorem partner (H : OneDirty G C g) :
    ∃ k < C.gates.length, (gateAt C k).op = GateOp.and ∧ ∃ z : Fin n, PZ C g k z := by
  obtain ⟨T, hT, hTo, c, hc⟩ := above_and H g H.hg H.dirty
  have hlt := opnd_lt C H.ao T hT (1 - c)
  have hnr := not_both' H T hT hTo c hc
  obtain ⟨z, _, hz⟩ := (pure_val H T hT hTo (1 - c) hnr (fun _ => true)).1 (ones_val C H.ao _ (by omega))
  exact ⟨T, hT, hTo, z, (pz_iff C g T z).2 ⟨c, hc, hz⟩⟩

/-- A low wire is true at some one-hot input. -/
theorem low_unit (H : OneDirty G C g) (v : Fin n) (hv : gateVal n C g (unitInput v) = true) (w : ℕ)
    (hw : w < n + C.gates.length) (hl : Low G C w) : ∃ y, wireVal n C w (unitInput y) = true := by
  rcases (val_low H w hw hl (fun _ => true)).1 (ones_val C H.ao w hw) with ⟨y, _, hy⟩ | ⟨hr, _⟩
  · exact ⟨y, hy⟩
  · exact ⟨v, (reach_le C H.ao g w hw hr).2 _ hv⟩

/-- The partner vertex is adjacent to the one-hot vertex of `g`. -/
theorem pz_v (H : OneDirty G C g) (v : Fin n) (hv : gateVal n C g (unitInput v) = true) (k : ℕ)
    (hk : k < C.gates.length) (ho : (gateAt C k).op = GateOp.and) (z : Fin n) (hz : PZ C g k z) :
    G.Adj v z := by
  apply pair_adj
  have hg := H.hg
  refine pz_F H k hk ho z hz _ ?_ (by simp [pairInput])
  exact mono C H.ao _ _ (unit_le v _ (by simp [pairInput])) (n + g) (by omega) hv

/-- Variables of the two operands of `g` off a partner vertex are adjacent. -/
theorem cross_adj (H : OneDirty G C g) (k : ℕ) (hk : k < C.gates.length)
    (ho : (gateAt C k).op = GateOp.and) (z : Fin n) (hz : PZ C g k z) (y y' : Fin n)
    (hy : wireVal n C (opnd C g 0) (unitInput y) = true)
    (hy' : wireVal n C (opnd C g 1) (unitInput y') = true)
    (hyz : ¬ G.Adj y z) (hyz' : ¬ G.Adj y' z) : G.Adj y y' := by
  have hF : graphFun G ∅ (fun a => decide (a = y ∨ a = y' ∨ a = z)) = true := by
    refine pz_F H k hk ho z hz _ ?_ (by simp)
    exact (val_and C H.ao g H.hg H.gand _).2
      ⟨(opnd_val H 0 _).2 ⟨y, by simp, hy⟩, (opnd_val H 1 _).2 ⟨y', by simp, hy'⟩⟩
  obtain ⟨u, w, huw, hu, hw⟩ := (graphFun_empty G _).1 hF
  simp only [decide_eq_true_eq] at hu hw
  rcases hu with hu | hu | hu <;> rcases hw with hw | hw | hw <;> rw [hu, hw] at huw
  · exact absurd huw (G.loopless.irrefl _)
  · exact huw
  · exact absurd huw hyz
  · exact huw.symm
  · exact absurd huw (G.loopless.irrefl _)
  · exact absurd huw hyz'
  · exact absurd huw.symm hyz
  · exact absurd huw.symm hyz'
  · exact absurd huw (G.loopless.irrefl _)

/-- A partner vertex is a variable of no operand of `g`. -/
theorem pz_off (H : OneDirty G C g)
    (hlast : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ∀ z : Fin n, PZ C g k z →
      (∃ y : Fin n, wireVal n C (opnd C g 0) (unitInput y) = true ∧ ¬ G.Adj y z) ∧
      (∃ y : Fin n, wireVal n C (opnd C g 1) (unitInput y) = true ∧ ¬ G.Adj y z))
    (k : ℕ) (hk : k < C.gates.length) (ho : (gateAt C k).op = GateOp.and) (z : Fin n) (hz : PZ C g k z)
    (c : Fin 2) (hzc : wireVal n C (opnd C g c) (unitInput z) = true) : False := by
  obtain ⟨⟨y, hy, hny⟩, ⟨y', hy', hny'⟩⟩ := hlast k hk ho z hz
  fin_cases c
  · exact hny' (pz_opnd H k hk ho z hz y' 0 hzc hy').symm
  · exact hny (pz_opnd H k hk ho z hz y 1 hzc hy).symm

/-- No AND other than `g` reads, through ORs, a gate with variables of both colours. -/
theorem no_read (H : OneDirty G C g) (s : Fin n → Bool) (v : Fin n)
    (bip : ∀ a b : Fin n, G.Adj a b → s a ≠ s b) (hv : gateVal n C g (unitInput v) = true)
    (h : ℕ) (_hh : h < C.gates.length) (hmix : Mix C s v (n + h))
    (k : ℕ) (hk : k < C.gates.length) (ho : (gateAt C k).op = GateOp.and) (hkg : k ≠ g) (c : Fin 2)
    (hr : OrReaches n C (opnd C k c) h) : False := by
  obtain ⟨y0, y1, hy0, hy1, e0, e1⟩ := hmix
  have hlt := opnd_lt C H.ao k hk c
  have hlt' := opnd_lt C H.ao k hk (1 - c)
  have hup := (reach_le C H.ao h _ (by omega) hr).2
  obtain ⟨y, hy⟩ := low_unit H v hv _ (by omega) (low_opnd H k hk (1 - c) (Or.inr ho))
  have a0 := and_pair' H k hk ho hkg c y0 y (hup _ hy0) hy
  have a1 := and_pair' H k hk ho hkg c y1 y (hup _ hy1) hy
  have h01 := col s y0 y1 y (bip _ _ a0) (bip _ _ a1)
  exact e1 (h01.symm.trans e0)

/-- A least wire with variables of both colours is an OR gate before `g`, one operand of one colour. -/
theorem find_h (H : OneDirty G C g) (s : Fin n → Bool) (v : Fin n) (w : ℕ) (hw : w < n + g)
    (hm : Mix C s v w) :
    ∃ h < g, (gateAt C h).op = GateOp.or ∧ Mix C s v (n + h) ∧ ∃ c0 : Fin 2,
      ∀ y, wireVal n C (opnd C h c0) (unitInput y) = true → s y ≠ s v := by
  classical
  have hex : ∃ w, Mix C s v w := ⟨w, hm⟩
  obtain ⟨m, hmm, hmin⟩ : ∃ m, Mix C s v m ∧ ∀ w' < m, ¬ Mix C s v w' :=
    ⟨Nat.find hex, Nat.find_spec hex, fun w' hw' => Nat.find_min hex hw'⟩
  have hle : m ≤ w := by
    by_contra hc
    exact hmin w (by omega) hm
  have hg := H.hg
  obtain ⟨y0, y1, h0, h1, e0, e1⟩ := hmm
  have hmn : n ≤ m := by
    by_contra hlt
    have hlt' : m < n := by omega
    rw [wireVal_lt C m hlt'] at h0 h1
    simp only [unitInput, decide_eq_true_eq] at h0 h1
    rw [← h0] at e0
    rw [← h1] at e1
    exact e1 e0
  have e : n + (m - n) = m := by omega
  have hh : m - n < C.gates.length := by omega
  have hlow : Low G C (n + (m - n)) := by
    intro hb
    have h3 := hb (unitInput y0) (by rw [e]; exact h0)
    rw [unit_false] at h3
    exact Bool.false_ne_true h3
  have hor : (gateAt C (m - n)).op = GateOp.or := by
    rcases LeafBound.ao_op H.ao hh with ho | ho
    · have := low_and H (m - n) hh ho hlow
      omega
    · exact ho
  have hgv : gateVal n C (m - n) (unitInput y1) = true := by
    show wireVal n C (n + (m - n)) _ = true
    rw [e]; exact h1
  refine ⟨m - n, by omega, hor, ⟨y0, y1, by rw [e]; exact h0, by rw [e]; exact h1, e0, e1⟩, ?_⟩
  rcases (val_or C H.ao (m - n) hh hor _).1 hgv with hc | hc
  · refine ⟨0, fun y hy heq => hmin _ ?_ ⟨y, y1, hy, hc, heq, e1⟩⟩
    have := opnd_lt C H.ao (m - n) hh 0
    omega
  · refine ⟨1, fun y hy heq => hmin _ ?_ ⟨y, y1, hy, hc, heq, e1⟩⟩
    have := opnd_lt C H.ao (m - n) hh 1
    omega

/-- Zero the one-colour operand of the OR gate `h`: a smaller circuit. -/
theorem core (H : OneDirty G C g) (s : Fin n → Bool) (v : Fin n)
    (bip : ∀ a b : Fin n, G.Adj a b → s a ≠ s b) (hv : gateVal n C g (unitInput v) = true)
    (hlast : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ∀ z : Fin n, PZ C g k z →
      (∃ y : Fin n, wireVal n C (opnd C g 0) (unitInput y) = true ∧ ¬ G.Adj y z) ∧
      (∃ y : Fin n, wireVal n C (opnd C g 1) (unitInput y) = true ∧ ¬ G.Adj y z))
    (h : ℕ) (hhg : h < g) (hor : (gateAt C h).op = GateOp.or) (hmix : Mix C s v (n + h)) (c0 : Fin 2)
    (hz : ∀ y, wireVal n C (opnd C h c0) (unitInput y) = true → s y ≠ s v) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size < C.size ∧ circuitFun n D = graphFun G ∅ := by
  classical
  have hAO := H.ao
  have hg := H.hg
  have hh : h < C.gates.length := by omega
  obtain ⟨o, hol, hoo, hob⟩ := out_gate H
  have hmix' := hmix
  obtain ⟨y0, y1, hy0, hy1, e0, e1⟩ := hmix'
  have hlowh : Low G C (n + h) := by
    intro hb
    have h3 := hb (unitInput y0) hy0
    rw [unit_false] at h3
    exact Bool.false_ne_true h3
  refine redirect_lt G C (Finset.range C.gates.length) (fun k hk => Finset.mem_range.1 hk) (rho n C h c0) ?_
    (srcOf n C.output) ?_ (adj_of_AO G C hAO H.comp (by omega)) ?_ ?_ ⟨h, hh, Or.inr ⟨c0, rho_cut C h c0⟩⟩
  · intro k hk b j hj
    have hkl := Finset.mem_range.1 hk
    by_cases hkb : k = h ∧ b = c0
    · rw [hkb.1, hkb.2, rho_cut C h c0] at hj
      cases hj
    · rw [rho_keep C h c0 k b hkb] at hj
      have h1 := srcOf_inr _ _ hj
      have h2 := opnd_lt C hAO k hkl b
      exact ⟨Finset.mem_range.2 (by omega), by omega⟩
  · intro j hj
    have h1 := srcOf_inr _ _ hj
    exact Finset.mem_range.2 (by omega)
  · intro x hx
    refine ⟨fun j => gateVal n C j x, super_of_le C hAO _ (fun k hk => Finset.mem_range.1 hk) _ x ?_, ?_⟩
    · intro k _ b hb
      by_cases hkb : k = h ∧ b = c0
      · rw [hkb.1, hkb.2, rho_cut C h c0] at hb
        exact absurd hb Bool.false_ne_true
      · rw [rho_keep C h c0 k b hkb, srcAt_srcOf] at hb
        exact hb
    · rw [srcAt_srcOf]
      have h1 : circuitFun n C x = false := by rw [H.comp]; exact hx
      exact h1
  · intro p q hpq
    obtain ⟨e, he⟩ : ∃ e : Fin n → Bool, e = pairInput p q := ⟨_, rfl⟩
    rw [← he]
    have hFe : graphFun G ∅ e = true := by
      rw [he]
      exact (graphFun_empty G _).2 ⟨p, q, hpq, by simp [pairInput], by simp [pairInput]⟩
    have hle : ∀ a, xcol s v e a = true → e a = true := fun a ha => ((xcol_iff s v e a).1 ha).1
    have hea : ∀ a b : Fin n, e a = true → e b = true → a ≠ b → G.Adj a b := by
      intro a b ha hb hab
      rw [he] at ha hb
      simp only [pairInput, decide_eq_true_eq] at ha hb
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · exact absurd (ha.trans hb.symm) hab
      · rw [ha, hb]; exact hpq
      · rw [ha, hb]; exact hpq.symm
      · exact absurd (ha.trans hb.symm) hab
    refine ⟨uval n C h g e (xcol s v e), ?_, ?_⟩
    · intro k hk huk
      have hkl := Finset.mem_range.1 hk
      show opv (isA (gateAt C k).op) _ _ = true
      by_cases hkh : k = h
      · rw [hkh] at huk ⊢
        rw [uval_pos C h g e _ h (Or.inl (reach_self C hAO h hh))] at huk
        rw [hor]
        show opv false _ _ = true
        rw [opv_or]
        have hl0 := opnd_lt C hAO h hh c0
        have hl1 := opnd_lt C hAO h hh (1 - c0)
        rcases (val_or' C hAO h hh hor _ c0).1 huk with h0 | h1
        · exfalso
          rcases (val_low H _ (by omega) (low_opnd H h hh c0 (Or.inl hlowh)) _).1 h0 with ⟨y, hyx, hy⟩ | ⟨hr, _⟩
          · exact hz y hy ((xcol_iff s v e y).1 hyx).2
          · have := (reach_le C hAO g _ (by omega) hr).1
            omega
        · refine fin2_pick c0 (fun b => srcAt e (uval n C h g e (xcol s v e)) (rho n C h c0 h b) = true) ?_
          show srcAt e (uval n C h g e (xcol s v e)) (rho n C h c0 h (1 - c0)) = true
          rw [rho_keep C h c0 h (1 - c0) (fun hh' => fin2_ne' c0 hh'.2)]
          exact U_low C hAO h g e _ hle _ (by omega) h1
      · have hk0 : ¬ (k = h ∧ (0 : Fin 2) = c0) := fun hh' => hkh hh'.1
        have hk1 : ¬ (k = h ∧ (1 : Fin 2) = c0) := fun hh' => hkh hh'.1
        have hl0 := opnd_lt C hAO k hkl 0
        have hl1 := opnd_lt C hAO k hkl 1
        rw [rho_keep C h c0 k 0 hk0, rho_keep C h c0 k 1 hk1]
        by_cases hd : Dep n C h g (n + k)
        · rw [uval_pos C h g e _ k hd, gate_eq C hAO k hkl] at huk
          exact opv_mono _ _ _ _ _ (U_low C hAO h g e _ hle _ (by omega)) (U_low C hAO h g e _ hle _ (by omega)) huk
        · rw [uval_neg C h g e _ k hd] at huk
          rcases LeafBound.ao_op hAO hkl with ho | ho
          · rw [ho]
            show opv true _ _ = true
            rw [opv_and]
            have hkg : k ≠ g := fun hkg => hd (Or.inr (by rw [hkg]; exact reach_self C hAO g hg))
            have key : ∀ c : Fin 2, srcAt e (uval n C h g e (xcol s v e)) (srcOf n (opnd C k c)) = true := by
              intro c
              have hlt := opnd_lt C hAO k hkl c
              obtain ⟨hwc, hw'⟩ := (val_and' C hAO k hkl ho e c).1 huk
              have hL1 : ¬ OrReaches n C (opnd C k c) h :=
                fun hr => no_read H s v bip hv h hh hmix k hkl ho hkg c hr
              by_cases hr : OrReaches n C (opnd C k c) g
              · refine U_low C hAO h g e _ hle _ (by omega) ?_
                have hnr := not_both' H k hkl ho c hr
                obtain ⟨z', hz'e, hz'⟩ := (pure_val H k hkl ho (1 - c) hnr e).1 hw'
                have hpz : PZ C g k z' := (pz_iff C g k z').2 ⟨c, hr, hz'⟩
                have hvz : G.Adj v z' := pz_v H v hv k hkl ho z' hpz
                rcases (val_low H _ (by omega) (low_opnd H k hkl c (Or.inr ho)) e).1 hwc with
                  ⟨y, hye, hy⟩ | ⟨_, hge⟩
                · have hadj := and_pair' H k hkl ho hkg c y z' hy hz'
                  have hs : s y = s v := col s y v z' (bip _ _ hadj) (bip _ _ hvz)
                  exact mono C hAO _ _ (unit_le y _ ((xcol_iff s v e y).2 ⟨hye, hs⟩)) _ (by omega) hy
                · refine (reach_le C hAO g _ (by omega) hr).2 _ ?_
                  obtain ⟨ha, hb⟩ := (val_and C hAO g hg H.gand e).1 hge
                  obtain ⟨a, hae, hVa⟩ := (opnd_val H 0 e).1 ha
                  obtain ⟨b, hbe, hVb⟩ := (opnd_val H 1 e).1 hb
                  have haz : a ≠ z' := fun h' => pz_off H hlast k hkl ho z' hpz 0 (by rw [← h']; exact hVa)
                  have hbz : b ≠ z' := fun h' => pz_off H hlast k hkl ho z' hpz 1 (by rw [← h']; exact hVb)
                  have hsa : s a = s v := col s a v z' (bip _ _ (hea a z' hae hz'e haz)) (bip _ _ hvz)
                  have hsb : s b = s v := col s b v z' (bip _ _ (hea b z' hbe hz'e hbz)) (bip _ _ hvz)
                  exact (val_and C hAO g hg H.gand _).2
                    ⟨(opnd_val H 0 _).2 ⟨a, (xcol_iff s v e a).2 ⟨hae, hsa⟩, hVa⟩,
                      (opnd_val H 1 _).2 ⟨b, (xcol_iff s v e b).2 ⟨hbe, hsb⟩, hVb⟩⟩
              · exact U_free C h g e _ _ (fun hd' => hd'.elim hL1 hr) hwc
            exact ⟨key 0, key 1⟩
          · rw [ho]
            show opv false _ _ = true
            rw [opv_or]
            have hnd : ∀ b : Fin 2, ¬ Dep n C h g (opnd C k b) := fun b hdb =>
              hd (hdb.elim (fun h1 => Or.inl ((reach_gate C hAO k h hkl).2 (Or.inr ⟨ho, b, h1⟩)))
                (fun h1 => Or.inr ((reach_gate C hAO k g hkl).2 (Or.inr ⟨ho, b, h1⟩))))
            rcases (val_or C hAO k hkl ho e).1 huk with h0 | h1
            · exact Or.inl (U_free C h g e _ _ (hnd 0) h0)
            · exact Or.inr (U_free C h g e _ _ (hnd 1) h1)
    · refine U_free C h g e _ _ ?_ ?_
      · rw [hoo]
        rintro (hd | hd)
        · have h1 := (reach_le C hAO h _ (by omega) hd).2 _ hy0
          have h3 := hob _ h1
          rw [unit_false] at h3
          exact Bool.false_ne_true h3
        · have h1 := (reach_le C hAO g _ (by omega) hd).2 _ hv
          have h3 := hob _ h1
          rw [unit_false] at h3
          exact Bool.false_ne_true h3
      · have h1 : circuitFun n C e = true := by rw [H.comp]; exact hFe
        exact h1

/-- The step: a circuit of this kind is not least. -/
theorem final (H : OneDirty G C g) (s : Fin n → Bool) (v : Fin n)
    (bip : ∀ a b : Fin n, G.Adj a b → s a ≠ s b) (hv : gateVal n C g (unitInput v) = true)
    (hlast : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ∀ z : Fin n, PZ C g k z →
      (∃ y : Fin n, wireVal n C (opnd C g 0) (unitInput y) = true ∧ ¬ G.Adj y z) ∧
      (∃ y : Fin n, wireVal n C (opnd C g 1) (unitInput y) = true ∧ ¬ G.Adj y z)) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size < C.size ∧ circuitFun n D = graphFun G ∅ := by
  obtain ⟨k, hk, ho, z, hzp⟩ := partner H
  obtain ⟨⟨y, hy, hny⟩, ⟨y', hy', hny'⟩⟩ := hlast k hk ho z hzp
  have hadj := cross_adj H k hk ho z hzp y y' hy hy' hny hny'
  obtain ⟨hv0, hv1⟩ := (val_and C H.ao g H.hg H.gand _).1 hv
  have hne := bip _ _ hadj
  have hmixw : ∃ c : Fin 2, Mix C s v (opnd C g c) := by
    by_cases hc : s y' = s v
    · exact ⟨0, v, y, hv0, hy, rfl, fun h' => hne (h'.trans hc.symm)⟩
    · exact ⟨1, v, y', hv1, hy', rfl, hc⟩
  obtain ⟨c, hm⟩ := hmixw
  obtain ⟨h, hhg, hor, hmix, c0, hz0⟩ := find_h H s v _ (opnd_lt C H.ao g H.hg c) hm
  exact core H s v bip hv hlast h hhg hor hmix c0 hz0

end

end PEqualNP.Outside.L_meta_4741_aux

theorem PEqualNP.Outside.L_meta_4741 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (g : ℕ) (v : Fin n), (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C → (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ t ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs, ¬ (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, t⟩ (List.ofFn x) = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true)) → (∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k) → g < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and → ¬ PEqualNP.TopForm.BelowF G C g → (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → k ≠ g → PEqualNP.TopForm.BelowF G C k) → PEqualNP.EdgeOwnership.gateVal n C g (PEqualNP.SplitCount.unitInput v) = true → (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ z : Fin n, (PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C k 0) g ∧ PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C k 1) (PEqualNP.SplitCount.unitInput z) = true) ∨ (PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C k 1) g ∧ PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C k 0) (PEqualNP.SplitCount.unitInput z) = true) → (∃ y : Fin n, PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C g 0) (PEqualNP.SplitCount.unitInput y) = true ∧ ¬ G.Adj y z) ∧ (∃ y : Fin n, PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C g 1) (PEqualNP.SplitCount.unitInput y) = true ∧ ¬ G.Adj y z)) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n D ∧ D.size < C.size ∧ PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
  intro n G _ C s g v bip _ hAO hcomp hlift handLow hcone hg hgand hdirty hothers hv hlast
  exact PEqualNP.Outside.L_meta_4741_aux.final
    ⟨hAO, hcomp, hlift, handLow, hcone, hg, hgand, hdirty, hothers⟩ s v bip hv hlast
