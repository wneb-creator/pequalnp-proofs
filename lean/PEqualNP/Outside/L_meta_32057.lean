import PEqualNP.Defs
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Data.Int.Lemmas

namespace PEqualNP.Outside.L_meta_32057_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

abbrev F2 := ZMod 2

def legalGates (n : ℕ) (gs : List Gate) : Prop :=
  ReadsBack n ⟨gs, 0⟩ ∧
    ∀ h ∈ gs, h.inputs.length ≤ 2 ∧
      (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1))

noncomputable def costGates (gs : List Gate) : ℕ :=
  gs.countP (fun h => @decide ((h.op = .and ∨ h.op = .or) ∧ h.inputs.length = 2) (Classical.propDecidable _))

def wiresOf (gs : List Gate) (x : List Bool) : List Bool :=
  (Circuit.mk gs 0).wires x

def bitsOf (n : ℕ) (u : Fin n → F2) : List Bool :=
  List.ofFn (fun j : Fin n => decide (u j = 1))

lemma bitsOf_len (n : ℕ) (u : Fin n → F2) : (bitsOf n u).length = n := by
  simp [bitsOf]

lemma bitsOf_getD (n : ℕ) (u : Fin n → F2) (j : Fin n) :
    (bitsOf n u).getD j.val false = decide (u j = 1) := by
  simp [bitsOf, List.getD_eq_getElem?_getD, j.isLt]

lemma zmod2_add_decide (a b : F2) :
    decide (a + b = 1) = Bool.xor (decide (a = 1)) (decide (b = 1)) := by
  fin_cases a <;> fin_cases b <;> decide

lemma zmod2_mul_decide (a b : F2) :
    decide (a * b = 1) = (decide (a = 1) && decide (b = 1)) := by
  fin_cases a <;> fin_cases b <;> decide

lemma zmod2_bool_decide (b : Bool) :
    decide ((if b then (1 : F2) else 0) = 1) = b := by
  cases b <;> decide

lemma zmod2_cases (a : F2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma zmod2_xor_zero_iff (b ow : Bool) (d : F2) :
    d + (if Bool.xor b ow then (1 : F2) else 0) = 0 ↔ b = Bool.xor ow (decide (d = 1)) := by
  cases b <;> cases ow <;> fin_cases d <;> decide

lemma zmod2_decide_bool (a : F2) :
    (if decide (a = 1) then (1 : F2) else 0) = a := by
  fin_cases a <;> rfl

lemma zmod2_sub_eq_add (a b : F2) : a - b = a + b := by
  fin_cases a <;> fin_cases b <;> decide

lemma zmod2_vec_sub_eq_add {k : ℕ} (x y : Fin k → F2) : x - y = x + y := by
  funext j; exact zmod2_sub_eq_add (x j) (y j)

lemma zmod2_vec_add_self {k : ℕ} (x : Fin k → F2) : x + x = 0 := by
  funext j
  have : x j + x j = 0 := by
    rcases zmod2_cases (x j) with h | h <;> rw [h] <;> decide
  exact this

lemma wiresOf_len (gs : List Gate) (x : List Bool) :
    (wiresOf gs x).length = x.length + gs.length := by
  unfold wiresOf Circuit.wires
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
    omega

lemma wiresOf_append (gs1 gs2 : List Gate) (x : List Bool) :
    wiresOf (gs1 ++ gs2) x = wiresOf gs2 (wiresOf gs1 x) := by
  unfold wiresOf Circuit.wires
  exact List.foldl_append

lemma wiresOf_getD_lt (gs : List Gate) (x : List Bool) {i : ℕ} (hi : i < x.length) :
    (wiresOf gs x).getD i false = x.getD i false := by
  unfold wiresOf Circuit.wires
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hi' : i < (x ++ [g.op.eval (g.inputs.map fun idx => x.getD idx false)]).length := by
      simp only [List.length_append, List.length_cons, List.length_nil]; omega
    rw [ih _ hi']
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma wiresOf_append_getD_lt (gs1 gs2 : List Gate) (x : List Bool) {i : ℕ}
    (hi : i < x.length + gs1.length) :
    (wiresOf (gs1 ++ gs2) x).getD i false = (wiresOf gs1 x).getD i false := by
  rw [wiresOf_append, wiresOf_getD_lt gs2 (wiresOf gs1 x) (by rw [wiresOf_len]; exact hi)]

lemma wiresOf_snoc_last (gs : List Gate) (g : Gate) (x : List Bool) :
    (wiresOf (gs ++ [g]) x).getD (x.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (wiresOf gs x).getD i false) := by
  rw [wiresOf_append]
  set w := wiresOf gs x
  have hlen : w.length = x.length + gs.length := wiresOf_len gs x
  change (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).getD (x.length + gs.length) false = _
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
      show x.length + gs.length - w.length = 0 by omega]
  rfl

lemma wiresOf_snoc_last_eq {n : ℕ} (gs : List Gate) (g : Gate) (x : List Bool) (hx : x.length = n) :
    (wiresOf (gs ++ [g]) x).getD (n + gs.length) false =
      g.op.eval (g.inputs.map fun i => (wiresOf gs x).getD i false) := by
  have h := wiresOf_snoc_last gs g x
  rw [hx] at h
  exact h

lemma readsBack_append {n : ℕ} {gs1 gs2 : List Gate}
    (h1 : ReadsBack n ⟨gs1, 0⟩)
    (h2 : ∀ j < gs2.length, ∀ i ∈ (gs2.getD j ⟨.or, []⟩).inputs, i < n + gs1.length + j) :
    ReadsBack n ⟨gs1 ++ gs2, 0⟩ := by
  intro j hj i hi
  simp only [gateAt] at hi
  simp only [List.length_append] at hj
  by_cases hlt : j < gs1.length
  · have hget : (gs1 ++ gs2).getD j ⟨.or, []⟩ = gs1.getD j ⟨.or, []⟩ := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
    rw [hget] at hi
    exact h1 j hlt i hi
  · have hge : gs1.length ≤ j := by omega
    have hget : (gs1 ++ gs2).getD j ⟨.or, []⟩ = gs2.getD (j - gs1.length) ⟨.or, []⟩ := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hge]
    rw [hget] at hi
    have := h2 (j - gs1.length) (by omega) i hi
    omega

lemma legalGates_snoc {n : ℕ} {gs : List Gate} {g : Gate}
    (hgs : legalGates n gs)
    (hback : ∀ i ∈ g.inputs, i < n + gs.length)
    (hshape : g.inputs.length ≤ 2 ∧
      (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))) :
    legalGates n (gs ++ [g]) := by
  refine ⟨readsBack_append hgs.1 ?_, ?_⟩
  · intro j hj i hi
    have hj0 : j = 0 := by simp at hj; omega
    subst hj0
    simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero, Option.getD_some] at hi
    have := hback i hi
    omega
  · intro h hh
    rcases List.mem_append.mp hh with h1 | h2
    · exact hgs.2 h h1
    · simp only [List.mem_singleton] at h2; subst h2; exact hshape

lemma legalGates_prefix {n : ℕ} {gs : List Gate} {g : Gate}
    (h : legalGates n (gs ++ [g])) :
    legalGates n gs ∧
      (∀ i ∈ g.inputs, i < n + gs.length) ∧
      (g.inputs.length ≤ 2 ∧
        (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))) := by
  refine ⟨⟨?_, fun h' hh' => h.2 h' (List.mem_append_left _ hh')⟩, ?_, h.2 g (by simp)⟩
  · intro j hj i hi
    have hj0 : j < gs.length := hj
    have hj' : j < (gs ++ [g]).length := by simp; omega
    have hget : (gs ++ [g]).getD j ⟨.or, []⟩ = gs.getD j ⟨.or, []⟩ := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hj0]
    have hi' : i ∈ (gateAt ⟨gs ++ [g], 0⟩ j).inputs := by
      change i ∈ ((gs ++ [g]).getD j ⟨.or, []⟩).inputs
      rw [hget]; exact hi
    exact h.1 j hj' i hi'
  · intro i hi
    have hj' : gs.length < (gs ++ [g]).length := by simp
    have hget : (gs ++ [g]).getD gs.length ⟨.or, []⟩ = g := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self,
        List.getElem?_cons_zero, Option.getD_some]
    exact h.1 gs.length hj' i (by simpa [gateAt, hget] using hi)

lemma costGates_append (gs1 gs2 : List Gate) :
    costGates (gs1 ++ gs2) = costGates gs1 + costGates gs2 := by
  unfold costGates; exact List.countP_append

lemma costGates_snoc_zero (gs : List Gate) (g : Gate)
    (h0 : ¬ ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2)) :
    costGates (gs ++ [g]) = costGates gs := by
  rw [costGates_append]
  unfold costGates
  simp [h0]

lemma costGates_snoc_one (gs : List Gate) (g : Gate)
    (h1 : (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) :
    costGates (gs ++ [g]) = costGates gs + 1 := by
  rw [costGates_append]
  unfold costGates
  simp [h1]

lemma addXor_step (t : ℕ) (gs : List Gate) (w1 w2 : ℕ)
    (hgs : legalGates t gs) (hw1 : w1 < t + gs.length) (hw2 : w2 < t + gs.length) :
    let gs' := gs ++ [⟨.mod 2, [w1, w2]⟩, ⟨.not, [t + gs.length]⟩]
    legalGates t gs' ∧
    costGates gs' = costGates gs ∧
    gs'.length = gs.length + 2 ∧
    ∀ x : List Bool, x.length = t →
      (wiresOf gs' x).getD (t + gs.length + 1) false =
        Bool.xor ((wiresOf gs x).getD w1 false) ((wiresOf gs x).getD w2 false) := by
  intro gs'
  have h1 : legalGates t (gs ++ [⟨.mod 2, [w1, w2]⟩]) := by
    apply legalGates_snoc hgs
    · intro i hi; simp at hi; rcases hi with rfl | rfl <;> omega
    · exact ⟨by simp, Or.inr (Or.inr (Or.inl rfl))⟩
  have h2 : legalGates t ((gs ++ [⟨.mod 2, [w1, w2]⟩]) ++ [⟨.not, [t + gs.length]⟩]) := by
    apply legalGates_snoc h1
    · intro i hi; simp at hi; subst hi; simp
    · exact ⟨by simp, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
  have hgs'_eq : gs' = (gs ++ [⟨.mod 2, [w1, w2]⟩]) ++ [⟨.not, [t + gs.length]⟩] := by simp [gs']
  refine ⟨hgs'_eq ▸ h2, ?_, by simp [gs'], ?_⟩
  · rw [hgs'_eq,
        costGates_snoc_zero (gs ++ [(⟨.mod 2, [w1, w2]⟩ : Gate)]) (⟨.not, [t + gs.length]⟩ : Gate) (by simp),
        costGates_snoc_zero gs (⟨.mod 2, [w1, w2]⟩ : Gate) (by simp)]
  · intro x hx
    rw [hgs'_eq]
    have hidx : t + gs.length + 1 = x.length + (gs ++ [(⟨.mod 2, [w1, w2]⟩ : Gate)]).length := by simp; omega
    rw [hidx, wiresOf_snoc_last]
    have hidx1 : t + gs.length = x.length + gs.length := by omega
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.headD_cons]
    rw [hidx1, wiresOf_snoc_last]
    simp only [List.map_cons, List.map_nil, GateOp.eval]
    cases (wiresOf gs x).getD w1 false <;> cases (wiresOf gs x).getD w2 false <;> decide

def addXorMany (t cWire : ℕ) (flag : ℕ → Bool) (old : ℕ → ℕ) :
    ℕ → List Gate → List Gate × (ℕ → ℕ)
  | 0, gs => (gs, old)
  | m + 1, gs =>
    let res := addXorMany t cWire flag old m gs
    let gs1 := res.1
    let f1 := res.2
    if flag m then
      (gs1 ++ [⟨.mod 2, [old m, cWire]⟩, ⟨.not, [t + gs1.length]⟩],
        fun u => if u = m then t + gs1.length + 1 else f1 u)
    else (gs1, f1)

lemma addXorMany_spec (t cWire : ℕ) (flag : ℕ → Bool) (old : ℕ → ℕ) :
    ∀ (m : ℕ) (gs : List Gate),
      legalGates t gs →
      cWire < t + gs.length →
      (∀ u < m, old u < t + gs.length) →
      let res := addXorMany t cWire flag old m gs
      ∃ ext : List Gate,
        res.1 = gs ++ ext ∧
        legalGates t res.1 ∧
        costGates res.1 = costGates gs ∧
        (∀ u < m, res.2 u < t + res.1.length) ∧
        (∀ u < m, ∀ x : List Bool, x.length = t →
          (wiresOf res.1 x).getD (res.2 u) false =
            if flag u then
              Bool.xor ((wiresOf gs x).getD (old u) false) ((wiresOf gs x).getD cWire false)
            else (wiresOf gs x).getD (old u) false) := by
  intro m
  induction m with
  | zero =>
    intro gs hleg _ _
    exact ⟨[], by simp [addXorMany], hleg, rfl, fun _ hu => by omega, fun _ hu => by omega⟩
  | succ m ih =>
    intro gs hleg hc hold
    rcases ih gs hleg hc (fun u hu => hold u (by omega)) with ⟨ext1, h1eq, h1leg, h1cost, h1lt, h1sem⟩
    set gs1 := (addXorMany t cWire flag old m gs).1
    set f1 := (addXorMany t cWire flag old m gs).2
    have hlen1 : gs.length ≤ gs1.length := by rw [h1eq, List.length_append]; omega
    by_cases hfl : flag m = true
    · have hstep := addXor_step t gs1 (old m) cWire h1leg
        (by have := hold m (by omega); omega) (by omega)
      refine ⟨ext1 ++ [⟨.mod 2, [old m, cWire]⟩, ⟨.not, [t + gs1.length]⟩], ?_, ?_, ?_, ?_, ?_⟩
      · simp [addXorMany, hfl, gs1, h1eq, List.append_assoc]
      · simpa [addXorMany, hfl, gs1] using hstep.1
      · simpa [addXorMany, hfl, gs1, h1cost] using hstep.2.1
      · intro u hu
        simp only [addXorMany, hfl, ↓reduceIte]
        by_cases hum : u = m
        · subst hum; simp only [↓reduceIte, List.length_append, List.length_cons, List.length_nil]; omega
        · simp only [hum, ↓reduceIte, List.length_append, List.length_cons, List.length_nil]
          have := h1lt u (by omega); dsimp only [gs1, f1] at this; omega
      · intro u hu x hx
        simp only [addXorMany, hfl, ↓reduceIte]
        by_cases hum : u = m
        · subst hum
          simp only [↓reduceIte, hfl]
          change (wiresOf (gs1 ++ [⟨.mod 2, [old u, cWire]⟩, ⟨.not, [t + gs1.length]⟩]) x).getD (t + gs1.length + 1) false = _
          rw [hstep.2.2.2 x hx, h1eq,
              wiresOf_append_getD_lt gs ext1 x (by rw [hx]; exact hold u (by omega)),
              wiresOf_append_getD_lt gs ext1 x (by rw [hx]; exact hc)]
        · simp only [hum, ↓reduceIte]
          change (wiresOf (gs1 ++ [⟨.mod 2, [old m, cWire]⟩, ⟨.not, [t + gs1.length]⟩]) x).getD (f1 u) false = _
          rw [wiresOf_append_getD_lt gs1 _ x (by rw [hx]; exact h1lt u (by omega))]
          exact h1sem u (by omega) x hx
    · have hflf : flag m = false := Bool.eq_false_iff.mpr hfl
      refine ⟨ext1, ?_, ?_, ?_, ?_, ?_⟩
      · simp [addXorMany, hflf, gs1, h1eq]
      · simpa [addXorMany, hflf, gs1] using h1leg
      · simpa [addXorMany, hflf, gs1] using h1cost
      · intro u hu
        simp only [addXorMany, hflf, Bool.false_eq_true, ↓reduceIte]
        by_cases hum : u = m
        · subst hum
          have hfm : (addXorMany t cWire flag old u gs).2 u = old u := by
            clear h1eq h1leg h1cost h1lt h1sem hlen1 ih
            have hkeep : ∀ (n : ℕ) (g : List Gate), u ≥ n → (addXorMany t cWire flag old n g).2 u = old u := by
              intro n
              induction n with
              | zero => intro g _; rfl
              | succ n ihn =>
                intro g hge
                simp only [addXorMany]
                split_ifs
                · have hne : u ≠ n := by omega
                  simp only [hne, ↓reduceIte]
                  exact ihn g (by omega)
                · exact ihn g (by omega)
            exact hkeep u gs (le_refl _)
          rw [hfm]; have := hold u (by omega); dsimp only [gs1] at hlen1; omega
        · exact h1lt u (by omega)
      · intro u hu x hx
        simp only [addXorMany, hflf, Bool.false_eq_true, ↓reduceIte]
        by_cases hum : u = m
        · subst hum
          have hfm : (addXorMany t cWire flag old u gs).2 u = old u := by
            clear h1eq h1leg h1cost h1lt h1sem hlen1 ih
            have hkeep : ∀ (n : ℕ) (g : List Gate), u ≥ n → (addXorMany t cWire flag old n g).2 u = old u := by
              intro n
              induction n with
              | zero => intro g _; rfl
              | succ n ihn =>
                intro g hge
                simp only [addXorMany]
                split_ifs
                · have hne : u ≠ n := by omega
                  simp only [hne, ↓reduceIte]
                  exact ihn g (by omega)
                · exact ihn g (by omega)
            exact hkeep u gs (le_refl _)
          rw [hfm, hflf]
          simp only [Bool.false_eq_true, ↓reduceIte]
          change (wiresOf gs1 x).getD (old u) false = _
          rw [h1eq, wiresOf_append_getD_lt gs ext1 x (by rw [hx]; exact hold u (by omega))]
        · exact h1sem u (by omega) x hx

def dotLin {k : ℕ} (s0 : Fin k → F2) : (Fin k → F2) →ₗ[F2] F2 :=
  { toFun := fun u => dotProduct s0 u
    map_add' := fun a b => dotProduct_add s0 a b
    map_smul' := fun c a => by simp [dotProduct_smul] }

def kerDot {k : ℕ} (U : Submodule F2 (Fin k → F2)) (s0 : Fin k → F2) : Submodule F2 (Fin k → F2) :=
  U ⊓ LinearMap.ker (dotLin s0)

lemma mem_kerDot {k : ℕ} (U : Submodule F2 (Fin k → F2)) (s0 u : Fin k → F2) :
    u ∈ kerDot U s0 ↔ u ∈ U ∧ dotProduct s0 u = 0 := Iff.rfl

lemma finrank_ker_dot {k : ℕ} (U : Submodule F2 (Fin k → F2)) (s0 v0 : Fin k → F2)
    (hv0 : v0 ∈ U) (hdot : dotProduct s0 v0 = 1) :
    Module.finrank F2 (kerDot U s0) + 1 = Module.finrank F2 U := by
  let φ : U →ₗ[F2] F2 :=
    { toFun := fun u => dotProduct s0 u.val
      map_add' := fun a b => dotProduct_add s0 a.val b.val
      map_smul' := fun c a => by simp [dotProduct_smul] }
  have hsurj : Function.Surjective φ := by
    intro c
    refine ⟨c • ⟨v0, hv0⟩, ?_⟩
    simp only [map_smul, φ, LinearMap.coe_mk, AddHom.coe_mk, hdot, smul_eq_mul, mul_one]
  have hrk := LinearMap.finrank_range_add_finrank_ker φ
  have hran : LinearMap.range φ = ⊤ := LinearMap.range_eq_top.mpr hsurj
  rw [hran, finrank_top, Module.finrank_self] at hrk
  have hequiv : kerDot U s0 ≃ₗ[F2] LinearMap.ker φ :=
    { toFun := fun u => ⟨⟨u.val, u.property.1⟩, u.property.2⟩
      invFun := fun u => ⟨u.val.val, ⟨u.val.property, u.property⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  rw [hequiv.finrank_eq]
  omega

abbrev Branch (k t : ℕ) : Type :=
  ℕ × Submodule F2 (Fin k → F2) × List Gate ×
    (Fin k → ℕ) × (ℕ → ℕ) × (ℕ → Fin k → F2)

abbrev Branch.r {k t : ℕ} (B : Branch k t) : ℕ := B.1
abbrev Branch.U {k t : ℕ} (B : Branch k t) : Submodule F2 (Fin k → F2) := B.2.1
abbrev Branch.gates {k t : ℕ} (B : Branch k t) : List Gate := B.2.2.1
abbrev Branch.tap {k t : ℕ} (B : Branch k t) : Fin k → ℕ := B.2.2.2.1
abbrev Branch.off {k t : ℕ} (B : Branch k t) : ℕ → ℕ := B.2.2.2.2.1
abbrev Branch.slope {k t : ℕ} (B : Branch k t) : ℕ → Fin k → F2 := B.2.2.2.2.2

lemma branch_r_mk {k t : ℕ} (r : ℕ) (U : Submodule F2 (Fin k → F2))
    (gs : List Gate) (tap : Fin k → ℕ) (off : ℕ → ℕ) (slope : ℕ → Fin k → F2) :
    Branch.r (k := k) (t := t) ⟨r, U, gs, tap, off, slope⟩ = r := rfl

lemma branch_U_mk {k t : ℕ} (r : ℕ) (U : Submodule F2 (Fin k → F2))
    (gs : List Gate) (tap : Fin k → ℕ) (off : ℕ → ℕ) (slope : ℕ → Fin k → F2) :
    Branch.U (k := k) (t := t) ⟨r, U, gs, tap, off, slope⟩ = U := rfl

lemma branch_gates_mk {k t : ℕ} (r : ℕ) (U : Submodule F2 (Fin k → F2))
    (gs : List Gate) (tap : Fin k → ℕ) (off : ℕ → ℕ) (slope : ℕ → Fin k → F2) :
    Branch.gates (k := k) (t := t) ⟨r, U, gs, tap, off, slope⟩ = gs := rfl

lemma branch_tap_mk {k t : ℕ} (r : ℕ) (U : Submodule F2 (Fin k → F2))
    (gs : List Gate) (tap : Fin k → ℕ) (off : ℕ → ℕ) (slope : ℕ → Fin k → F2) :
    Branch.tap (k := k) (t := t) ⟨r, U, gs, tap, off, slope⟩ = tap := rfl

lemma branch_off_mk {k t : ℕ} (r : ℕ) (U : Submodule F2 (Fin k → F2))
    (gs : List Gate) (tap : Fin k → ℕ) (off : ℕ → ℕ) (slope : ℕ → Fin k → F2) :
    Branch.off (k := k) (t := t) ⟨r, U, gs, tap, off, slope⟩ = off := rfl

lemma branch_slope_mk {k t : ℕ} (r : ℕ) (U : Submodule F2 (Fin k → F2))
    (gs : List Gate) (tap : Fin k → ℕ) (off : ℕ → ℕ) (slope : ℕ → Fin k → F2) :
    Branch.slope (k := k) (t := t) ⟨r, U, gs, tap, off, slope⟩ = slope := rfl

def Branch.pos {k t : ℕ} (B : Branch k t) (z : Fin t → F2) (j : Fin k) : F2 :=
  if (wiresOf B.gates (bitsOf t z)).getD (B.tap j) false then 1 else 0

def ValidBranch {k t : ℕ} (gs : List Gate) (B : Branch k t) : Prop :=
  Module.finrank F2 B.U + B.r = k ∧
  legalGates t B.gates ∧
  costGates B.gates + B.r ≤ costGates gs ∧
  (∀ j : Fin k, B.tap j < t + B.gates.length) ∧
  (∀ w < k + t + gs.length, B.off w < t + B.gates.length) ∧
  (∀ w < k + t + gs.length, ∀ (z : Fin t → F2) (u : Fin k → F2), u ∈ B.U →
    (wiresOf gs (bitsOf k (B.pos z + u) ++ bitsOf t z)).getD w false =
      Bool.xor ((wiresOf B.gates (bitsOf t z)).getD (B.off w) false)
        (decide (dotProduct (B.slope w) u = 1)))

lemma branch_eval_add_gate {k t : ℕ} {gs : List Gate} {g : Gate} {B : Branch k t}
    (_hleg : legalGates (k + t) (gs ++ [g]))
    (hB : ValidBranch gs B)
    (gs' : List Gate) (ext : List Gate) (hgs' : gs' = B.gates ++ ext)
    (hleg' : legalGates t gs')
    (hcost' : costGates gs' + B.r ≤ costGates (gs ++ [g]))
    (wNew : ℕ) (hwNew : wNew < t + gs'.length) (sNew : Fin k → F2)
    (hsemNew : ∀ (z : Fin t → F2) (u : Fin k → F2), u ∈ B.U →
      g.op.eval (g.inputs.map fun i => (wiresOf gs (bitsOf k (B.pos z + u) ++ bitsOf t z)).getD i false) =
        Bool.xor ((wiresOf gs' (bitsOf t z)).getD wNew false) (decide (dotProduct sNew u = 1))) :
    let B' : Branch k t :=
      ⟨B.r, B.U, gs', B.tap,
        fun w => if w = k + t + gs.length then wNew else B.off w,
        fun w => if w = k + t + gs.length then sNew else B.slope w⟩
    ValidBranch (gs ++ [g]) B' ∧
      ∀ z : Fin t → F2, B'.pos z = B.pos z := by
  intro B'
  have hpos_eq : ∀ z : Fin t → F2, B'.pos z = B.pos z := by
    intro z; funext j
    simp only [branch_gates_mk, branch_tap_mk, Branch.pos, B', hgs']
    rw [wiresOf_append_getD_lt B.gates ext (bitsOf t z) (by rw [bitsOf_len]; exact hB.2.2.2.1 j)]
  refine ⟨⟨hB.1, hleg', hcost', ?_, ?_, ?_⟩, hpos_eq⟩
  · intro j; simp only [branch_gates_mk, branch_tap_mk, B', hgs', List.length_append]; have := hB.2.2.2.1 j; omega
  · intro w hw
    simp only [List.length_append, List.length_cons, List.length_nil] at hw
    simp only [branch_gates_mk, branch_off_mk, B']
    by_cases hweq : w = k + t + gs.length
    · simp only [hweq, ↓reduceIte]; exact hwNew
    · simp only [hweq, ↓reduceIte, hgs', List.length_append]
      have := hB.2.2.2.2.1 w (by omega); omega
  · intro w hw z u hu
    simp only [List.length_append, List.length_cons, List.length_nil] at hw
    rw [hpos_eq z]
    have hlen_in : (bitsOf k (B.pos z + u) ++ bitsOf t z).length = k + t := by
      simp [bitsOf_len]
    by_cases hweq : w = k + t + gs.length
    · subst hweq
      simp only [branch_gates_mk, branch_off_mk, branch_slope_mk, B', ↓reduceIte]
      have hidx : k + t + gs.length = (bitsOf k (B.pos z + u) ++ bitsOf t z).length + gs.length := by omega
      rw [hidx, wiresOf_snoc_last]
      exact hsemNew z u hu
    · simp only [branch_gates_mk, branch_off_mk, branch_slope_mk, B', hweq, ↓reduceIte]
      rw [wiresOf_append_getD_lt gs [g] _ (by rw [hlen_in]; omega)]
      rw [hgs', wiresOf_append_getD_lt B.gates ext (bitsOf t z) (by rw [bitsOf_len]; exact hB.2.2.2.2.1 w (by omega))]
      exact hB.2.2.2.2.2 w (by omega) z u hu

lemma step_single_branch {k t : ℕ} {gs : List Gate} {g : Gate} (B : Branch k t)
    (hleg : legalGates (k + t) (gs ++ [g])) (hB : ValidBranch gs B) :
    ∃ L : List (Branch k t),
      (∀ B' ∈ L, ValidBranch (gs ++ [g]) B') ∧
      ∀ (z : Fin t → F2) (x : Fin k → F2),
        (x - B.pos z ∈ B.U → ∃! idx : Fin L.length, x - (L.get idx).pos z ∈ (L.get idx).U) ∧
        (x - B.pos z ∉ B.U → ∀ idx : Fin L.length, x - (L.get idx).pos z ∉ (L.get idx).U) := by
  have hpre := legalGates_prefix hleg
  have hback := hpre.2.1
  have hshape := hpre.2.2
  have hcost_ge : costGates gs ≤ costGates (gs ++ [g]) := by
    rw [costGates_append]; omega
  have hwrap_one : ∀ (B' : Branch k t), ValidBranch (gs ++ [g]) B' → B'.U = B.U →
      (∀ z, B'.pos z = B.pos z) →
      ∃ L : List (Branch k t),
        (∀ b ∈ L, ValidBranch (gs ++ [g]) b) ∧
        ∀ (z : Fin t → F2) (x : Fin k → F2),
          (x - B.pos z ∈ B.U → ∃! idx : Fin L.length, x - (L.get idx).pos z ∈ (L.get idx).U) ∧
          (x - B.pos z ∉ B.U → ∀ idx : Fin L.length, x - (L.get idx).pos z ∉ (L.get idx).U) := by
    intro B' hB' hU hpos
    refine ⟨[B'], fun b hb => by simp at hb; subst hb; exact hB', fun z x => ⟨?_, ?_⟩⟩
    · intro hx
      refine ⟨⟨0, by simp⟩, by simpa [hpos, hU] using hx, fun j _ => Fin.ext (by have := j.isLt; simp only [List.length_singleton] at this; change j.val = 0; omega)⟩
    · intro hnx idx
      have hi0 : idx = ⟨0, by simp⟩ := Fin.ext (by have := idx.isLt; simp only [List.length_singleton] at this; change idx.val = 0; omega)
      subst hi0
      simpa [hpos, hU] using hnx
  rcases hshape.2 with hop | hop | hop | ⟨hop, hlen1⟩
  ·
    rcases hg : g.inputs with _ | ⟨w0, rest⟩
    ·
      let gs' := B.gates ++ [⟨.and, []⟩]
      have hleg' : legalGates t gs' :=
        legalGates_snoc hB.2.1 (by simp) ⟨by simp, Or.inl rfl⟩
      have hcost' : costGates gs' + B.r ≤ costGates (gs ++ [g]) := by
        rw [costGates_snoc_zero B.gates _ (by simp)]; have := hB.2.2.1; omega
      have hres := branch_eval_add_gate hleg hB gs' [⟨.and, []⟩] rfl hleg' hcost'
        (t + B.gates.length) (by simp [gs']) 0 (fun z u _ => by
          rw [hop, hg]
          have hidx : t + B.gates.length = (bitsOf t z).length + B.gates.length := by rw [bitsOf_len]
          rw [hidx, wiresOf_snoc_last]; simp [GateOp.eval])
      exact hwrap_one _ hres.1 rfl hres.2
    · rcases rest with _ | ⟨w1, rest2⟩
      ·
        have hw0 : w0 < k + t + gs.length := hback w0 (by rw [hg]; simp)
        have hres := branch_eval_add_gate hleg hB B.gates [] (by simp) hB.2.1
          (by have := hB.2.2.1; omega) (B.off w0) (hB.2.2.2.2.1 w0 hw0) (B.slope w0)
          (fun z u hu => by
            rw [hop, hg]; simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons,
              List.all_nil, id_eq, Bool.and_true]
            exact hB.2.2.2.2.2 w0 hw0 z u hu)
        exact hwrap_one _ hres.1 rfl hres.2
      · rcases rest2 with _ | ⟨_, _⟩
        ·
          have hw0 : w0 < k + t + gs.length := hback w0 (by rw [hg]; simp)
          have hw1 : w1 < k + t + gs.length := hback w1 (by rw [hg]; simp)
          have hcost1 : costGates (gs ++ [g]) = costGates gs + 1 :=
            costGates_snoc_one gs g ⟨Or.inl hop, by rw [hg]; rfl⟩
          by_cases hvan : (∀ u ∈ B.U, dotProduct (B.slope w0) u = 0) ∧
              (∀ u ∈ B.U, dotProduct (B.slope w1) u = 0)
          ·
            let gs' := B.gates ++ [⟨.and, [B.off w0, B.off w1]⟩]
            have hleg' : legalGates t gs' :=
              legalGates_snoc hB.2.1
                (fun i hi => by simp at hi; rcases hi with rfl | rfl; exact hB.2.2.2.2.1 w0 hw0; exact hB.2.2.2.2.1 w1 hw1)
                ⟨by simp, Or.inl rfl⟩
            have hcost' : costGates gs' + B.r ≤ costGates (gs ++ [g]) := by
              rw [costGates_snoc_one B.gates _ ⟨Or.inl rfl, rfl⟩, hcost1]; have := hB.2.2.1; omega
            have hres := branch_eval_add_gate hleg hB gs' [⟨.and, [B.off w0, B.off w1]⟩] rfl hleg' hcost'
              (t + B.gates.length) (by simp [gs']) 0 (fun z u hu => by
                rw [hop, hg]
                have hidx : t + B.gates.length = (bitsOf t z).length + B.gates.length := by rw [bitsOf_len]
                rw [hidx, wiresOf_snoc_last]
                simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
                  id_eq, Bool.and_true]
                rw [hB.2.2.2.2.2 w0 hw0 z u hu, hB.2.2.2.2.2 w1 hw1 z u hu,
                    hvan.1 u hu, hvan.2 u hu]
                simp)
            exact hwrap_one _ hres.1 rfl hres.2
          ·
            have hex : ∃ (wa wb : ℕ), wa < k + t + gs.length ∧ wb < k + t + gs.length ∧
                ((wa = w0 ∧ wb = w1) ∨ (wa = w1 ∧ wb = w0)) ∧
                ∃ v0 ∈ B.U, dotProduct (B.slope wa) v0 = 1 := by
              by_cases h0 : ∀ u ∈ B.U, dotProduct (B.slope w0) u = 0
              · have h1 : ¬ ∀ u ∈ B.U, dotProduct (B.slope w1) u = 0 := fun h => hvan ⟨h0, h⟩
                push Not at h1
                rcases h1 with ⟨v0, hv0, hne⟩
                have hd1 : dotProduct (B.slope w1) v0 = 1 := by
                  rcases zmod2_cases (dotProduct (B.slope w1) v0) with h | h
                  · exact absurd h hne
                  · exact h
                exact ⟨w1, w0, hw1, hw0, Or.inr ⟨rfl, rfl⟩, v0, hv0, hd1⟩
              · push Not at h0
                rcases h0 with ⟨v0, hv0, hne⟩
                have hd1 : dotProduct (B.slope w0) v0 = 1 := by
                  rcases zmod2_cases (dotProduct (B.slope w0) v0) with h | h
                  · exact absurd h hne
                  · exact h
                exact ⟨w0, w1, hw0, hw1, Or.inl ⟨rfl, rfl⟩, v0, hv0, hd1⟩
            rcases hex with ⟨wa, wb, hwa, hwb, hwab, v0, hv0, hdot⟩
            let U' : Submodule F2 (Fin k → F2) := kerDot B.U (B.slope wa)
            have hdim' : Module.finrank F2 U' + (B.r + 1) = k := by
              have h1 : Module.finrank F2 U' + 1 = Module.finrank F2 B.U :=
                finrank_ker_dot B.U (B.slope wa) v0 hv0 hdot
              have h2 := hB.1
              omega
            have hbuild_child : ∀ (b : Bool), ∃ Bc : Branch k t,
                ValidBranch (gs ++ [g]) Bc ∧ Bc.U = U' ∧
                ∀ z : Fin t → F2,
                  Bc.pos z = B.pos z +
                    (if Bool.xor b ((wiresOf B.gates (bitsOf t z)).getD (B.off wa) false) then (1 : F2) else 0) • v0 := by
              intro b
              let gs0 := if b then B.gates ++ [⟨.not, [B.off wa]⟩] else B.gates
              let cWire := if b then t + B.gates.length else B.off wa
              have hgs0_ext : ∃ e0, gs0 = B.gates ++ e0 := by
                cases b
                · exact ⟨[], by simp [gs0]⟩
                · exact ⟨[⟨.not, [B.off wa]⟩], rfl⟩
              have hgs0_leg : legalGates t gs0 := by
                cases b
                · exact hB.2.1
                · exact legalGates_snoc hB.2.1 (fun i hi => by simp at hi; subst hi; exact hB.2.2.2.2.1 wa hwa)
                    ⟨by simp, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
              have hgs0_cost : costGates gs0 = costGates B.gates := by
                cases b
                · rfl
                · exact costGates_snoc_zero B.gates _ (by simp)
              have hcWire_lt : cWire < t + gs0.length := by
                cases b
                · exact hB.2.2.2.2.1 wa hwa
                · simp [gs0, cWire]
              have hcWire_sem : ∀ z : Fin t → F2,
                  (wiresOf gs0 (bitsOf t z)).getD cWire false =
                    Bool.xor b ((wiresOf B.gates (bitsOf t z)).getD (B.off wa) false) := by
                intro z
                cases b
                · simp [gs0, cWire]
                · simp only [gs0, cWire, ↓reduceIte]
                  have hidx : t + B.gates.length = (bitsOf t z).length + B.gates.length := by rw [bitsOf_len]
                  rw [hidx, wiresOf_snoc_last]
                  simp [GateOp.eval]
              let tapOld : ℕ → ℕ := fun j => if hj : j < k then B.tap ⟨j, hj⟩ else 0
              let flagTap : ℕ → Bool := fun j => if hj : j < k then decide (v0 ⟨j, hj⟩ = 1) else false
              let resT := addXorMany t cWire flagTap tapOld k gs0
              have hresT := addXorMany_spec t cWire flagTap tapOld k gs0 hgs0_leg hcWire_lt
                (fun j hj => by
                  simp only [tapOld, hj, ↓reduceDIte]
                  rcases hgs0_ext with ⟨e0, he0⟩
                  rw [he0, List.length_append]
                  have := hB.2.2.2.1 ⟨j, hj⟩; omega)
              rcases hresT with ⟨extT, hTeq, hTleg, hTcost, hTlt, hTsem⟩
              let flagOff : ℕ → Bool := fun w => decide (dotProduct (B.slope w) v0 = 1)
              let resO := addXorMany t cWire flagOff B.off (k + t + gs.length) resT.1
              have hresO := addXorMany_spec t cWire flagOff B.off (k + t + gs.length) resT.1 hTleg
                (by rw [hTeq, List.length_append]; omega)
                (fun w hw => by
                  rcases hgs0_ext with ⟨e0, he0⟩
                  rw [hTeq, he0, List.length_append, List.length_append]
                  have := hB.2.2.2.2.1 w hw; omega)
              rcases hresO with ⟨extO, hOeq, hOleg, hOcost, hOlt, hOsem⟩
              let gsF := if b then resO.1 else resO.1 ++ [⟨.or, []⟩]
              have hgsF_ext : ∃ eF, gsF = resO.1 ++ eF := by
                cases b
                · exact ⟨[⟨.or, []⟩], rfl⟩
                · exact ⟨[], by simp [gsF]⟩
              have hgsF_leg : legalGates t gsF := by
                cases b
                · exact legalGates_snoc hOleg (by simp) ⟨by simp, Or.inr (Or.inl rfl)⟩
                · exact hOleg
              have hgsF_cost : costGates gsF = costGates B.gates := by
                cases b
                · rw [show gsF = resO.1 ++ [⟨.or, []⟩] from rfl, costGates_snoc_zero _ _ (by simp), hOcost, hTcost, hgs0_cost]
                · simp only [gsF, ↓reduceIte]; rw [hOcost, hTcost, hgs0_cost]
              let tapF : Fin k → ℕ := fun j => resT.2 j.val
              let wNew := if b then resO.2 wb else t + resO.1.length
              let sNew : Fin k → F2 := if b then B.slope wb else 0
              let Bc : Branch k t :=
                ⟨B.r + 1, U', gsF, tapF,
                  fun w => if w = k + t + gs.length then wNew else resO.2 w,
                  fun w => if w = k + t + gs.length then sNew else B.slope w⟩
              have hpos_c : ∀ z : Fin t → F2,
                  Bc.pos z = B.pos z +
                    (if Bool.xor b ((wiresOf B.gates (bitsOf t z)).getD (B.off wa) false) then (1 : F2) else 0) • v0 := by
                intro z; funext j
                rcases hgsF_ext with ⟨eF, heF⟩
                rcases hgs0_ext with ⟨e0, he0⟩
                have htap_val : (wiresOf gsF (bitsOf t z)).getD (tapF j) false =
                    (wiresOf resT.1 (bitsOf t z)).getD (resT.2 j.val) false := by
                  rw [heF, hOeq, List.append_assoc,
                      wiresOf_append_getD_lt resT.1 _ (bitsOf t z) (by rw [bitsOf_len]; exact hTlt j.val j.isLt)]
                simp only [branch_gates_mk, branch_tap_mk, Branch.pos, Bc, htap_val]
                rw [hTsem j.val j.isLt (bitsOf t z) (bitsOf_len t z)]
                simp only [flagTap, tapOld, j.isLt, ↓reduceDIte, hcWire_sem z]
                rw [he0, wiresOf_append_getD_lt B.gates e0 (bitsOf t z) (by rw [bitsOf_len]; exact hB.2.2.2.1 j)]
                simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Branch.pos]
                cases (wiresOf B.gates (bitsOf t z)).getD (B.tap j) false <;>
                  cases Bool.xor b ((wiresOf B.gates (bitsOf t z)).getD (B.off wa) false) <;>
                  rcases zmod2_cases (v0 j) with h | h <;> simp [h] <;> decide
              have hsem_old : ∀ w < k + t + gs.length, ∀ (z : Fin t → F2) (u : Fin k → F2), u ∈ U' →
                  (wiresOf gs (bitsOf k (Bc.pos z + u) ++ bitsOf t z)).getD w false =
                    Bool.xor ((wiresOf gsF (bitsOf t z)).getD (resO.2 w) false)
                      (decide (dotProduct (B.slope w) u = 1)) := by
                intro w hw z u hu
                rcases hgsF_ext with ⟨eF, heF⟩
                rcases hgs0_ext with ⟨e0, he0⟩
                set cbit := Bool.xor b ((wiresOf B.gates (bitsOf t z)).getD (B.off wa) false)
                set cf : F2 := if cbit then 1 else 0
                have hu_in_B : cf • v0 + u ∈ B.U := B.U.add_mem (B.U.smul_mem cf hv0) hu.1
                have hpos_rw : Bc.pos z + u = B.pos z + (cf • v0 + u) := by
                  rw [hpos_c z, add_assoc]
                rw [hpos_rw, hB.2.2.2.2.2 w hw z (cf • v0 + u) hu_in_B]
                have hwireO : (wiresOf gsF (bitsOf t z)).getD (resO.2 w) false =
                    if decide (dotProduct (B.slope w) v0 = 1) then
                      Bool.xor ((wiresOf B.gates (bitsOf t z)).getD (B.off w) false) cbit
                    else (wiresOf B.gates (bitsOf t z)).getD (B.off w) false := by
                  rw [heF, wiresOf_append_getD_lt resO.1 eF (bitsOf t z) (by rw [bitsOf_len]; exact hOlt w hw)]
                  rw [hOsem w hw (bitsOf t z) (bitsOf_len t z)]
                  rw [hTeq,
                      wiresOf_append_getD_lt gs0 extT (bitsOf t z) (by rw [bitsOf_len, he0, List.length_append]; have := hB.2.2.2.2.1 w hw; omega),
                      wiresOf_append_getD_lt gs0 extT (bitsOf t z) (by rw [bitsOf_len]; exact hcWire_lt)]
                  rw [hcWire_sem z, he0, wiresOf_append_getD_lt B.gates e0 (bitsOf t z) (by rw [bitsOf_len]; exact hB.2.2.2.2.1 w hw)]
                rw [hwireO, dotProduct_add, dotProduct_smul, zmod2_add_decide, smul_eq_mul, zmod2_mul_decide, zmod2_bool_decide]
                cases (wiresOf B.gates (bitsOf t z)).getD (B.off w) false <;>
                  cases cbit <;> cases decide (dotProduct (B.slope w) v0 = 1) <;>
                  cases decide (dotProduct (B.slope w) u = 1) <;> decide
              refine ⟨Bc, ⟨hdim', hgsF_leg, by change costGates gsF + (B.r + 1) ≤ costGates (gs ++ [g]); rw [hgsF_cost, hcost1]; have := hB.2.2.1; omega, ?_, ?_, ?_⟩, rfl, hpos_c⟩
              · intro j
                rcases hgsF_ext with ⟨eF, heF⟩
                have h1 : resT.2 j.val < t + resT.1.length := hTlt j.val j.isLt
                have h2 : resO.1.length = resT.1.length + extO.length := by rw [hOeq, List.length_append]
                simp only [branch_gates_mk, branch_tap_mk, Bc, tapF, heF, List.length_append]
                omega
              · intro w hw
                simp only [List.length_append, List.length_cons, List.length_nil] at hw
                simp only [branch_gates_mk, branch_off_mk, Bc]
                by_cases hweq : w = k + t + gs.length
                · simp only [hweq, ↓reduceIte, wNew, gsF]
                  cases b
                  · simp
                  · simp only [↓reduceIte]; exact hOlt wb hwb
                · simp only [hweq, ↓reduceIte]
                  rcases hgsF_ext with ⟨eF, heF⟩
                  have h1 : resO.2 w < t + resO.1.length := hOlt w (by omega)
                  rw [heF, List.length_append]; omega
              · intro w hw z u hu
                simp only [List.length_append, List.length_cons, List.length_nil] at hw
                have hlen_in : (bitsOf k (Bc.pos z + u) ++ bitsOf t z).length = k + t := by simp [bitsOf_len]
                by_cases hweq : w = k + t + gs.length
                · subst hweq
                  simp only [branch_gates_mk, branch_off_mk, branch_slope_mk, Bc, ↓reduceIte]
                  rw [wiresOf_snoc_last_eq gs g _ hlen_in, hop, hg]
                  simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
                    id_eq, Bool.and_true]
                  have hwa_val : (wiresOf gs (bitsOf k (Bc.pos z + u) ++ bitsOf t z)).getD wa false = b := by
                    have hu2 : dotProduct (B.slope wa) u = 0 := hu.2
                    rw [hsem_old wa hwa z u hu, hu2]
                    rcases hgsF_ext with ⟨eF, heF⟩
                    rcases hgs0_ext with ⟨e0, he0⟩
                    rw [heF, wiresOf_append_getD_lt resO.1 eF (bitsOf t z) (by rw [bitsOf_len]; exact hOlt wa hwa)]
                    rw [hOsem wa hwa (bitsOf t z) (bitsOf_len t z)]
                    simp only [flagOff, hdot]
                    rw [hTeq,
                        wiresOf_append_getD_lt gs0 extT (bitsOf t z) (by rw [bitsOf_len, he0, List.length_append]; have := hB.2.2.2.2.1 wa hwa; omega),
                        wiresOf_append_getD_lt gs0 extT (bitsOf t z) (by rw [bitsOf_len]; exact hcWire_lt)]
                    rw [hcWire_sem z, he0, wiresOf_append_getD_lt B.gates e0 (bitsOf t z) (by rw [bitsOf_len]; exact hB.2.2.2.2.1 wa hwa)]
                    cases b <;> cases (wiresOf B.gates (bitsOf t z)).getD (B.off wa) false <;> decide
                  have hcomm : ((wiresOf gs (bitsOf k (Bc.pos z + u) ++ bitsOf t z)).getD w0 false &&
                      (wiresOf gs (bitsOf k (Bc.pos z + u) ++ bitsOf t z)).getD w1 false) =
                      ((wiresOf gs (bitsOf k (Bc.pos z + u) ++ bitsOf t z)).getD wa false &&
                       (wiresOf gs (bitsOf k (Bc.pos z + u) ++ bitsOf t z)).getD wb false) := by
                    rcases hwab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                    · rfl
                    · exact Bool.and_comm _ _
                  rw [hcomm, hwa_val]
                  cases b
                  · simp only [Bool.false_and, wNew, sNew, gsF, Bool.false_eq_true, ↓reduceIte]
                    rw [wiresOf_snoc_last_eq resO.1 ⟨.or, []⟩ (bitsOf t z) (bitsOf_len t z)]; simp [GateOp.eval]
                  · simp only [Bool.true_and, wNew, sNew, gsF, ↓reduceIte]
                    exact hsem_old wb hwb z u hu
                · simp only [branch_gates_mk, branch_off_mk, branch_slope_mk, Bc, hweq, ↓reduceIte]
                  rw [wiresOf_append_getD_lt gs [g] _ (by rw [hlen_in]; omega)]
                  exact hsem_old w (by omega) z u hu
            rcases hbuild_child false with ⟨B0, hB0, hU0, hpos0⟩
            rcases hbuild_child true with ⟨B1, hB1, hU1, hpos1⟩
            refine ⟨[B0, B1], ?_, ?_⟩
            · intro b hb; simp at hb; rcases hb with rfl | rfl; exact hB0; exact hB1
            · intro z x
              have hmem_iff : ∀ (b : Bool) (Bc : Branch k t), Bc.U = U' →
                  Bc.pos z = B.pos z + (if Bool.xor b ((wiresOf B.gates (bitsOf t z)).getD (B.off wa) false) then (1 : F2) else 0) • v0 →
                  (x - Bc.pos z ∈ Bc.U ↔
                    x - B.pos z ∈ B.U ∧
                      b = Bool.xor ((wiresOf B.gates (bitsOf t z)).getD (B.off wa) false)
                        (decide (dotProduct (B.slope wa) (x - B.pos z) = 1))) := by
                intro b Bc hUc hpc
                set ow := (wiresOf B.gates (bitsOf t z)).getD (B.off wa) false
                set cb := Bool.xor b ow
                set cf : F2 := if cb then 1 else 0
                have hdiff : x - Bc.pos z = (x - B.pos z) + cf • v0 := by
                  rw [hpc, zmod2_vec_sub_eq_add, zmod2_vec_sub_eq_add, add_assoc]
                rw [hUc, hdiff, mem_kerDot]
                constructor
                · rintro ⟨h1, h2⟩
                  have h1' : x - B.pos z ∈ B.U := by
                    have := B.U.add_mem h1 (B.U.smul_mem cf hv0)
                    rw [add_assoc, zmod2_vec_add_self, add_zero] at this
                    exact this
                  rw [dotProduct_add, dotProduct_smul, hdot, smul_eq_mul, mul_one] at h2
                  exact ⟨h1', (zmod2_xor_zero_iff b ow _).mp h2⟩
                · rintro ⟨h1, h2⟩
                  refine ⟨B.U.add_mem h1 (B.U.smul_mem cf hv0), ?_⟩
                  rw [dotProduct_add, dotProduct_smul, hdot, smul_eq_mul, mul_one]
                  exact (zmod2_xor_zero_iff b ow _).mpr h2
              constructor
              · intro hx
                cases htarget : Bool.xor ((wiresOf B.gates (bitsOf t z)).getD (B.off wa) false)
                    (decide (dotProduct (B.slope wa) (x - B.pos z) = 1))
                · refine ⟨⟨0, by simp⟩, ?_, ?_⟩
                  · exact (hmem_iff false B0 hU0 (hpos0 z)).mpr ⟨hx, htarget.symm⟩
                  · intro idx hidx
                    have hlt : idx.val < 2 := idx.isLt
                    interval_cases hv : idx.val
                    · exact Fin.ext hv
                    · exfalso
                      have hm : x - B1.pos z ∈ B1.U := by simpa [hv] using hidx
                      have := ((hmem_iff true B1 hU1 (hpos1 z)).mp hm).2
                      rw [htarget] at this; simp at this
                · refine ⟨⟨1, by simp⟩, ?_, ?_⟩
                  · exact (hmem_iff true B1 hU1 (hpos1 z)).mpr ⟨hx, htarget.symm⟩
                  · intro idx hidx
                    have hlt : idx.val < 2 := idx.isLt
                    interval_cases hv : idx.val
                    · exfalso
                      have hm : x - B0.pos z ∈ B0.U := by simpa [hv] using hidx
                      have := ((hmem_iff false B0 hU0 (hpos0 z)).mp hm).2
                      rw [htarget] at this; exact Bool.false_ne_true this
                    · exact Fin.ext hv
              · intro hnx idx hidx
                have hlt : idx.val < 2 := idx.isLt
                interval_cases hv : idx.val
                · have hm : x - B0.pos z ∈ B0.U := by simpa [hv] using hidx
                  exact hnx ((hmem_iff false B0 hU0 (hpos0 z)).mp hm).1
                · have hm : x - B1.pos z ∈ B1.U := by simpa [hv] using hidx
                  exact hnx ((hmem_iff true B1 hU1 (hpos1 z)).mp hm).1
        · exfalso; have := hshape.1; rw [hg] at this; simp at this
  ·
    rcases hg : g.inputs with _ | ⟨w0, rest⟩
    ·
      let gs' := B.gates ++ [⟨.or, []⟩]
      have hleg' : legalGates t gs' :=
        legalGates_snoc hB.2.1 (by simp) ⟨by simp, Or.inr (Or.inl rfl)⟩
      have hcost' : costGates gs' + B.r ≤ costGates (gs ++ [g]) := by
        rw [costGates_snoc_zero B.gates _ (by simp)]; have := hB.2.2.1; omega
      have hres := branch_eval_add_gate hleg hB gs' [⟨.or, []⟩] rfl hleg' hcost'
        (t + B.gates.length) (by simp [gs']) 0 (fun z u _ => by
          rw [hop, hg]
          have hidx : t + B.gates.length = (bitsOf t z).length + B.gates.length := by rw [bitsOf_len]
          rw [hidx, wiresOf_snoc_last]; simp [GateOp.eval])
      exact hwrap_one _ hres.1 rfl hres.2
    · rcases rest with _ | ⟨w1, rest2⟩
      ·
        have hw0 : w0 < k + t + gs.length := hback w0 (by rw [hg]; simp)
        have hres := branch_eval_add_gate hleg hB B.gates [] (by simp) hB.2.1
          (by have := hB.2.2.1; omega) (B.off w0) (hB.2.2.2.2.1 w0 hw0) (B.slope w0)
          (fun z u hu => by
            rw [hop, hg]; simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons,
              List.any_nil, id_eq, Bool.or_false]
            exact hB.2.2.2.2.2 w0 hw0 z u hu)
        exact hwrap_one _ hres.1 rfl hres.2
      · rcases rest2 with _ | ⟨_, _⟩
        ·
          have hw0 : w0 < k + t + gs.length := hback w0 (by rw [hg]; simp)
          have hw1 : w1 < k + t + gs.length := hback w1 (by rw [hg]; simp)
          have hcost1 : costGates (gs ++ [g]) = costGates gs + 1 :=
            costGates_snoc_one gs g ⟨Or.inr hop, by rw [hg]; rfl⟩
          by_cases hvan : (∀ u ∈ B.U, dotProduct (B.slope w0) u = 0) ∧
              (∀ u ∈ B.U, dotProduct (B.slope w1) u = 0)
          · let gs' := B.gates ++ [⟨.or, [B.off w0, B.off w1]⟩]
            have hleg' : legalGates t gs' :=
              legalGates_snoc hB.2.1
                (fun i hi => by simp at hi; rcases hi with rfl | rfl; exact hB.2.2.2.2.1 w0 hw0; exact hB.2.2.2.2.1 w1 hw1)
                ⟨by simp, Or.inr (Or.inl rfl)⟩
            have hcost' : costGates gs' + B.r ≤ costGates (gs ++ [g]) := by
              rw [costGates_snoc_one B.gates _ ⟨Or.inr rfl, rfl⟩, hcost1]; have := hB.2.2.1; omega
            have hres := branch_eval_add_gate hleg hB gs' [⟨.or, [B.off w0, B.off w1]⟩] rfl hleg' hcost'
              (t + B.gates.length) (by simp [gs']) 0 (fun z u hu => by
                rw [hop, hg]
                have hidx : t + B.gates.length = (bitsOf t z).length + B.gates.length := by rw [bitsOf_len]
                rw [hidx, wiresOf_snoc_last]
                simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
                  id_eq, Bool.or_false]
                rw [hB.2.2.2.2.2 w0 hw0 z u hu, hB.2.2.2.2.2 w1 hw1 z u hu,
                    hvan.1 u hu, hvan.2 u hu]
                simp)
            exact hwrap_one _ hres.1 rfl hres.2
          · have hex : ∃ (wa wb : ℕ), wa < k + t + gs.length ∧ wb < k + t + gs.length ∧
                ((wa = w0 ∧ wb = w1) ∨ (wa = w1 ∧ wb = w0)) ∧
                ∃ v0 ∈ B.U, dotProduct (B.slope wa) v0 = 1 := by
              by_cases h0 : ∀ u ∈ B.U, dotProduct (B.slope w0) u = 0
              · have h1 : ¬ ∀ u ∈ B.U, dotProduct (B.slope w1) u = 0 := fun h => hvan ⟨h0, h⟩
                push Not at h1
                rcases h1 with ⟨v0, hv0, hne⟩
                have hd1 : dotProduct (B.slope w1) v0 = 1 := by
                  rcases zmod2_cases (dotProduct (B.slope w1) v0) with h | h
                  · exact absurd h hne
                  · exact h
                exact ⟨w1, w0, hw1, hw0, Or.inr ⟨rfl, rfl⟩, v0, hv0, hd1⟩
              · push Not at h0
                rcases h0 with ⟨v0, hv0, hne⟩
                have hd1 : dotProduct (B.slope w0) v0 = 1 := by
                  rcases zmod2_cases (dotProduct (B.slope w0) v0) with h | h
                  · exact absurd h hne
                  · exact h
                exact ⟨w0, w1, hw0, hw1, Or.inl ⟨rfl, rfl⟩, v0, hv0, hd1⟩
            rcases hex with ⟨wa, wb, hwa, hwb, hwab, v0, hv0, hdot⟩
            let U' : Submodule F2 (Fin k → F2) := kerDot B.U (B.slope wa)
            have hdim' : Module.finrank F2 U' + (B.r + 1) = k := by
              have h1 : Module.finrank F2 U' + 1 = Module.finrank F2 B.U :=
                finrank_ker_dot B.U (B.slope wa) v0 hv0 hdot
              have h2 := hB.1
              omega
            have hbuild_child : ∀ (b : Bool), ∃ Bc : Branch k t,
                ValidBranch (gs ++ [g]) Bc ∧ Bc.U = U' ∧
                ∀ z : Fin t → F2,
                  Bc.pos z = B.pos z +
                    (if Bool.xor b ((wiresOf B.gates (bitsOf t z)).getD (B.off wa) false) then (1 : F2) else 0) • v0 := by
              intro b
              let gs0 := if b then B.gates ++ [⟨.not, [B.off wa]⟩] else B.gates
              let cWire := if b then t + B.gates.length else B.off wa
              have hgs0_ext : ∃ e0, gs0 = B.gates ++ e0 := by
                cases b
                · exact ⟨[], by simp [gs0]⟩
                · exact ⟨[⟨.not, [B.off wa]⟩], rfl⟩
              have hgs0_leg : legalGates t gs0 := by
                cases b
                · exact hB.2.1
                · exact legalGates_snoc hB.2.1 (fun i hi => by simp at hi; subst hi; exact hB.2.2.2.2.1 wa hwa)
                    ⟨by simp, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
              have hgs0_cost : costGates gs0 = costGates B.gates := by
                cases b
                · rfl
                · exact costGates_snoc_zero B.gates _ (by simp)
              have hcWire_lt : cWire < t + gs0.length := by
                cases b
                · exact hB.2.2.2.2.1 wa hwa
                · simp [gs0, cWire]
              have hcWire_sem : ∀ z : Fin t → F2,
                  (wiresOf gs0 (bitsOf t z)).getD cWire false =
                    Bool.xor b ((wiresOf B.gates (bitsOf t z)).getD (B.off wa) false) := by
                intro z
                cases b
                · simp [gs0, cWire]
                · simp only [gs0, cWire, ↓reduceIte]
                  have hidx : t + B.gates.length = (bitsOf t z).length + B.gates.length := by rw [bitsOf_len]
                  rw [hidx, wiresOf_snoc_last]
                  simp [GateOp.eval]
              let tapOld : ℕ → ℕ := fun j => if hj : j < k then B.tap ⟨j, hj⟩ else 0
              let flagTap : ℕ → Bool := fun j => if hj : j < k then decide (v0 ⟨j, hj⟩ = 1) else false
              let resT := addXorMany t cWire flagTap tapOld k gs0
              have hresT := addXorMany_spec t cWire flagTap tapOld k gs0 hgs0_leg hcWire_lt
                (fun j hj => by
                  simp only [tapOld, hj, ↓reduceDIte]
                  rcases hgs0_ext with ⟨e0, he0⟩
                  rw [he0, List.length_append]
                  have := hB.2.2.2.1 ⟨j, hj⟩; omega)
              rcases hresT with ⟨extT, hTeq, hTleg, hTcost, hTlt, hTsem⟩
              let flagOff : ℕ → Bool := fun w => decide (dotProduct (B.slope w) v0 = 1)
              let resO := addXorMany t cWire flagOff B.off (k + t + gs.length) resT.1
              have hresO := addXorMany_spec t cWire flagOff B.off (k + t + gs.length) resT.1 hTleg
                (by rw [hTeq, List.length_append]; omega)
                (fun w hw => by
                  rcases hgs0_ext with ⟨e0, he0⟩
                  rw [hTeq, he0, List.length_append, List.length_append]
                  have := hB.2.2.2.2.1 w hw; omega)
              rcases hresO with ⟨extO, hOeq, hOleg, hOcost, hOlt, hOsem⟩
              let gsF := if b then resO.1 ++ [⟨.and, []⟩] else resO.1
              have hgsF_ext : ∃ eF, gsF = resO.1 ++ eF := by
                cases b
                · exact ⟨[], by simp [gsF]⟩
                · exact ⟨[⟨.and, []⟩], rfl⟩
              have hgsF_leg : legalGates t gsF := by
                cases b
                · exact hOleg
                · exact legalGates_snoc hOleg (by simp) ⟨by simp, Or.inl rfl⟩
              have hgsF_cost : costGates gsF = costGates B.gates := by
                cases b
                · simp only [gsF, Bool.false_eq_true, ↓reduceIte]; rw [hOcost, hTcost, hgs0_cost]
                · rw [show gsF = resO.1 ++ [⟨.and, []⟩] from rfl, costGates_snoc_zero _ _ (by simp), hOcost, hTcost, hgs0_cost]
              let tapF : Fin k → ℕ := fun j => resT.2 j.val
              let wNew := if b then t + resO.1.length else resO.2 wb
              let sNew : Fin k → F2 := if b then 0 else B.slope wb
              let Bc : Branch k t :=
                ⟨B.r + 1, U', gsF, tapF,
                  fun w => if w = k + t + gs.length then wNew else resO.2 w,
                  fun w => if w = k + t + gs.length then sNew else B.slope w⟩
              have hpos_c : ∀ z : Fin t → F2,
                  Bc.pos z = B.pos z +
                    (if Bool.xor b ((wiresOf B.gates (bitsOf t z)).getD (B.off wa) false) then (1 : F2) else 0) • v0 := by
                intro z; funext j
                rcases hgsF_ext with ⟨eF, heF⟩
                rcases hgs0_ext with ⟨e0, he0⟩
                have htap_val : (wiresOf gsF (bitsOf t z)).getD (tapF j) false =
                    (wiresOf resT.1 (bitsOf t z)).getD (resT.2 j.val) false := by
                  rw [heF, hOeq, List.append_assoc,
                      wiresOf_append_getD_lt resT.1 _ (bitsOf t z) (by rw [bitsOf_len]; exact hTlt j.val j.isLt)]
                simp only [branch_gates_mk, branch_tap_mk, Branch.pos, Bc, htap_val]
                rw [hTsem j.val j.isLt (bitsOf t z) (bitsOf_len t z)]
                simp only [flagTap, tapOld, j.isLt, ↓reduceDIte, hcWire_sem z]
                rw [he0, wiresOf_append_getD_lt B.gates e0 (bitsOf t z) (by rw [bitsOf_len]; exact hB.2.2.2.1 j)]
                simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Branch.pos]
                cases (wiresOf B.gates (bitsOf t z)).getD (B.tap j) false <;>
                  cases Bool.xor b ((wiresOf B.gates (bitsOf t z)).getD (B.off wa) false) <;>
                  rcases zmod2_cases (v0 j) with h | h <;> simp [h] <;> decide
              have hsem_old : ∀ w < k + t + gs.length, ∀ (z : Fin t → F2) (u : Fin k → F2), u ∈ U' →
                  (wiresOf gs (bitsOf k (Bc.pos z + u) ++ bitsOf t z)).getD w false =
                    Bool.xor ((wiresOf gsF (bitsOf t z)).getD (resO.2 w) false)
                      (decide (dotProduct (B.slope w) u = 1)) := by
                intro w hw z u hu
                rcases hgsF_ext with ⟨eF, heF⟩
                rcases hgs0_ext with ⟨e0, he0⟩
                set cbit := Bool.xor b ((wiresOf B.gates (bitsOf t z)).getD (B.off wa) false)
                set cf : F2 := if cbit then 1 else 0
                have hu_in_B : cf • v0 + u ∈ B.U := B.U.add_mem (B.U.smul_mem cf hv0) hu.1
                have hpos_rw : Bc.pos z + u = B.pos z + (cf • v0 + u) := by
                  rw [hpos_c z, add_assoc]
                rw [hpos_rw, hB.2.2.2.2.2 w hw z (cf • v0 + u) hu_in_B]
                have hwireO : (wiresOf gsF (bitsOf t z)).getD (resO.2 w) false =
                    if decide (dotProduct (B.slope w) v0 = 1) then
                      Bool.xor ((wiresOf B.gates (bitsOf t z)).getD (B.off w) false) cbit
                    else (wiresOf B.gates (bitsOf t z)).getD (B.off w) false := by
                  rw [heF, wiresOf_append_getD_lt resO.1 eF (bitsOf t z) (by rw [bitsOf_len]; exact hOlt w hw)]
                  rw [hOsem w hw (bitsOf t z) (bitsOf_len t z)]
                  rw [hTeq,
                      wiresOf_append_getD_lt gs0 extT (bitsOf t z) (by rw [bitsOf_len, he0, List.length_append]; have := hB.2.2.2.2.1 w hw; omega),
                      wiresOf_append_getD_lt gs0 extT (bitsOf t z) (by rw [bitsOf_len]; exact hcWire_lt)]
                  rw [hcWire_sem z, he0, wiresOf_append_getD_lt B.gates e0 (bitsOf t z) (by rw [bitsOf_len]; exact hB.2.2.2.2.1 w hw)]
                rw [hwireO, dotProduct_add, dotProduct_smul, zmod2_add_decide, smul_eq_mul, zmod2_mul_decide, zmod2_bool_decide]
                cases (wiresOf B.gates (bitsOf t z)).getD (B.off w) false <;>
                  cases cbit <;> cases decide (dotProduct (B.slope w) v0 = 1) <;>
                  cases decide (dotProduct (B.slope w) u = 1) <;> decide
              refine ⟨Bc, ⟨hdim', hgsF_leg, by change costGates gsF + (B.r + 1) ≤ costGates (gs ++ [g]); rw [hgsF_cost, hcost1]; have := hB.2.2.1; omega, ?_, ?_, ?_⟩, rfl, hpos_c⟩
              · intro j
                rcases hgsF_ext with ⟨eF, heF⟩
                have h1 : resT.2 j.val < t + resT.1.length := hTlt j.val j.isLt
                have h2 : resO.1.length = resT.1.length + extO.length := by rw [hOeq, List.length_append]
                simp only [branch_gates_mk, branch_tap_mk, Bc, tapF, heF, List.length_append]
                omega
              · intro w hw
                simp only [List.length_append, List.length_cons, List.length_nil] at hw
                simp only [branch_gates_mk, branch_off_mk, Bc]
                by_cases hweq : w = k + t + gs.length
                · simp only [hweq, ↓reduceIte, wNew, gsF]
                  cases b
                  · simp only [Bool.false_eq_true, ↓reduceIte]; exact hOlt wb hwb
                  · simp
                · simp only [hweq, ↓reduceIte]
                  rcases hgsF_ext with ⟨eF, heF⟩
                  have h1 : resO.2 w < t + resO.1.length := hOlt w (by omega)
                  rw [heF, List.length_append]; omega
              · intro w hw z u hu
                simp only [List.length_append, List.length_cons, List.length_nil] at hw
                have hlen_in : (bitsOf k (Bc.pos z + u) ++ bitsOf t z).length = k + t := by simp [bitsOf_len]
                by_cases hweq : w = k + t + gs.length
                · subst hweq
                  simp only [branch_gates_mk, branch_off_mk, branch_slope_mk, Bc, ↓reduceIte]
                  rw [wiresOf_snoc_last_eq gs g _ hlen_in, hop, hg]
                  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
                    id_eq, Bool.or_false]
                  have hwa_val : (wiresOf gs (bitsOf k (Bc.pos z + u) ++ bitsOf t z)).getD wa false = b := by
                    have hu2 : dotProduct (B.slope wa) u = 0 := hu.2
                    rw [hsem_old wa hwa z u hu, hu2]
                    rcases hgsF_ext with ⟨eF, heF⟩
                    rcases hgs0_ext with ⟨e0, he0⟩
                    rw [heF, wiresOf_append_getD_lt resO.1 eF (bitsOf t z) (by rw [bitsOf_len]; exact hOlt wa hwa)]
                    rw [hOsem wa hwa (bitsOf t z) (bitsOf_len t z)]
                    simp only [flagOff, hdot]
                    rw [hTeq,
                        wiresOf_append_getD_lt gs0 extT (bitsOf t z) (by rw [bitsOf_len, he0, List.length_append]; have := hB.2.2.2.2.1 wa hwa; omega),
                        wiresOf_append_getD_lt gs0 extT (bitsOf t z) (by rw [bitsOf_len]; exact hcWire_lt)]
                    rw [hcWire_sem z, he0, wiresOf_append_getD_lt B.gates e0 (bitsOf t z) (by rw [bitsOf_len]; exact hB.2.2.2.2.1 wa hwa)]
                    cases b <;> cases (wiresOf B.gates (bitsOf t z)).getD (B.off wa) false <;> decide
                  have hcomm : ((wiresOf gs (bitsOf k (Bc.pos z + u) ++ bitsOf t z)).getD w0 false ||
                      (wiresOf gs (bitsOf k (Bc.pos z + u) ++ bitsOf t z)).getD w1 false) =
                      ((wiresOf gs (bitsOf k (Bc.pos z + u) ++ bitsOf t z)).getD wa false ||
                       (wiresOf gs (bitsOf k (Bc.pos z + u) ++ bitsOf t z)).getD wb false) := by
                    rcases hwab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                    · rfl
                    · exact Bool.or_comm _ _
                  rw [hcomm, hwa_val]
                  cases b
                  · simp only [Bool.false_or, wNew, sNew, gsF, Bool.false_eq_true, ↓reduceIte]
                    exact hsem_old wb hwb z u hu
                  · simp only [Bool.true_or, wNew, sNew, gsF, ↓reduceIte]
                    rw [wiresOf_snoc_last_eq resO.1 ⟨.and, []⟩ (bitsOf t z) (bitsOf_len t z)]; simp [GateOp.eval]
                · simp only [branch_gates_mk, branch_off_mk, branch_slope_mk, Bc, hweq, ↓reduceIte]
                  rw [wiresOf_append_getD_lt gs [g] _ (by rw [hlen_in]; omega)]
                  exact hsem_old w (by omega) z u hu
            rcases hbuild_child false with ⟨B0, hB0, hU0, hpos0⟩
            rcases hbuild_child true with ⟨B1, hB1, hU1, hpos1⟩
            refine ⟨[B0, B1], ?_, ?_⟩
            · intro b hb; simp at hb; rcases hb with rfl | rfl; exact hB0; exact hB1
            · intro z x
              have hmem_iff : ∀ (b : Bool) (Bc : Branch k t), Bc.U = U' →
                  Bc.pos z = B.pos z + (if Bool.xor b ((wiresOf B.gates (bitsOf t z)).getD (B.off wa) false) then (1 : F2) else 0) • v0 →
                  (x - Bc.pos z ∈ Bc.U ↔
                    x - B.pos z ∈ B.U ∧
                      b = Bool.xor ((wiresOf B.gates (bitsOf t z)).getD (B.off wa) false)
                        (decide (dotProduct (B.slope wa) (x - B.pos z) = 1))) := by
                intro b Bc hUc hpc
                set ow := (wiresOf B.gates (bitsOf t z)).getD (B.off wa) false
                set cb := Bool.xor b ow
                set cf : F2 := if cb then 1 else 0
                have hdiff : x - Bc.pos z = (x - B.pos z) + cf • v0 := by
                  rw [hpc, zmod2_vec_sub_eq_add, zmod2_vec_sub_eq_add, add_assoc]
                rw [hUc, hdiff, mem_kerDot]
                constructor
                · rintro ⟨h1, h2⟩
                  have h1' : x - B.pos z ∈ B.U := by
                    have := B.U.add_mem h1 (B.U.smul_mem cf hv0)
                    rw [add_assoc, zmod2_vec_add_self, add_zero] at this
                    exact this
                  rw [dotProduct_add, dotProduct_smul, hdot, smul_eq_mul, mul_one] at h2
                  exact ⟨h1', (zmod2_xor_zero_iff b ow _).mp h2⟩
                · rintro ⟨h1, h2⟩
                  refine ⟨B.U.add_mem h1 (B.U.smul_mem cf hv0), ?_⟩
                  rw [dotProduct_add, dotProduct_smul, hdot, smul_eq_mul, mul_one]
                  exact (zmod2_xor_zero_iff b ow _).mpr h2
              constructor
              · intro hx
                cases htarget : Bool.xor ((wiresOf B.gates (bitsOf t z)).getD (B.off wa) false)
                    (decide (dotProduct (B.slope wa) (x - B.pos z) = 1))
                · refine ⟨⟨0, by simp⟩, ?_, ?_⟩
                  · exact (hmem_iff false B0 hU0 (hpos0 z)).mpr ⟨hx, htarget.symm⟩
                  · intro idx hidx
                    have hlt : idx.val < 2 := idx.isLt
                    interval_cases hv : idx.val
                    · exact Fin.ext hv
                    · exfalso
                      have hm : x - B1.pos z ∈ B1.U := by simpa [hv] using hidx
                      have := ((hmem_iff true B1 hU1 (hpos1 z)).mp hm).2
                      rw [htarget] at this; simp at this
                · refine ⟨⟨1, by simp⟩, ?_, ?_⟩
                  · exact (hmem_iff true B1 hU1 (hpos1 z)).mpr ⟨hx, htarget.symm⟩
                  · intro idx hidx
                    have hlt : idx.val < 2 := idx.isLt
                    interval_cases hv : idx.val
                    · exfalso
                      have hm : x - B0.pos z ∈ B0.U := by simpa [hv] using hidx
                      have := ((hmem_iff false B0 hU0 (hpos0 z)).mp hm).2
                      rw [htarget] at this; exact Bool.false_ne_true this
                    · exact Fin.ext hv
              · intro hnx idx hidx
                have hlt : idx.val < 2 := idx.isLt
                interval_cases hv : idx.val
                · have hm : x - B0.pos z ∈ B0.U := by simpa [hv] using hidx
                  exact hnx ((hmem_iff false B0 hU0 (hpos0 z)).mp hm).1
                · have hm : x - B1.pos z ∈ B1.U := by simpa [hv] using hidx
                  exact hnx ((hmem_iff true B1 hU1 (hpos1 z)).mp hm).1
        · exfalso; have := hshape.1; rw [hg] at this; simp at this
  ·
    rcases hg : g.inputs with _ | ⟨w0, rest⟩
    ·
      let gs' := B.gates ++ [⟨.mod 2, []⟩]
      have hleg' : legalGates t gs' :=
        legalGates_snoc hB.2.1 (by simp) ⟨by simp, Or.inr (Or.inr (Or.inl rfl))⟩
      have hcost' : costGates gs' + B.r ≤ costGates (gs ++ [g]) := by
        rw [costGates_snoc_zero B.gates _ (by simp)]; have := hB.2.2.1; omega
      have hres := branch_eval_add_gate hleg hB gs' [⟨.mod 2, []⟩] rfl hleg' hcost'
        (t + B.gates.length) (by simp [gs']) 0 (fun z u _ => by
          rw [hop, hg]
          have hidx : t + B.gates.length = (bitsOf t z).length + B.gates.length := by rw [bitsOf_len]
          rw [hidx, wiresOf_snoc_last]; simp [GateOp.eval])
      exact hwrap_one _ hres.1 rfl hres.2
    · rcases rest with _ | ⟨w1, rest2⟩
      ·
        have hw0 : w0 < k + t + gs.length := hback w0 (by rw [hg]; simp)
        let gs' := B.gates ++ [⟨.not, [B.off w0]⟩]
        have hleg' : legalGates t gs' :=
          legalGates_snoc hB.2.1 (fun i hi => by simp at hi; subst hi; exact hB.2.2.2.2.1 w0 hw0)
            ⟨by simp, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
        have hcost' : costGates gs' + B.r ≤ costGates (gs ++ [g]) := by
          rw [costGates_snoc_zero B.gates _ (by simp)]; have := hB.2.2.1; omega
        have hres := branch_eval_add_gate hleg hB gs' [⟨.not, [B.off w0]⟩] rfl hleg' hcost'
          (t + B.gates.length) (by simp [gs']) (B.slope w0) (fun z u hu => by
            rw [hop, hg]
            have hidx : t + B.gates.length = (bitsOf t z).length + B.gates.length := by rw [bitsOf_len]
            rw [hidx, wiresOf_snoc_last]
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.headD_cons]
            rw [hB.2.2.2.2.2 w0 hw0 z u hu]
            cases (wiresOf B.gates (bitsOf t z)).getD (B.off w0) false <;>
              cases decide (dotProduct (B.slope w0) u = 1) <;> decide)
        exact hwrap_one _ hres.1 rfl hres.2
      · rcases rest2 with _ | ⟨_, _⟩
        ·
          have hw0 : w0 < k + t + gs.length := hback w0 (by rw [hg]; simp)
          have hw1 : w1 < k + t + gs.length := hback w1 (by rw [hg]; simp)
          let gs' := B.gates ++ [⟨.mod 2, [B.off w0, B.off w1]⟩]
          have hleg' : legalGates t gs' :=
            legalGates_snoc hB.2.1
              (fun i hi => by simp at hi; rcases hi with rfl | rfl; exact hB.2.2.2.2.1 w0 hw0; exact hB.2.2.2.2.1 w1 hw1)
              ⟨by simp, Or.inr (Or.inr (Or.inl rfl))⟩
          have hcost' : costGates gs' + B.r ≤ costGates (gs ++ [g]) := by
            rw [costGates_snoc_zero B.gates _ (by simp)]; have := hB.2.2.1; omega
          have hres := branch_eval_add_gate hleg hB gs' [⟨.mod 2, [B.off w0, B.off w1]⟩] rfl hleg' hcost'
            (t + B.gates.length) (by simp [gs']) (B.slope w0 + B.slope w1) (fun z u hu => by
              rw [hop, hg]
              have hidx : t + B.gates.length = (bitsOf t z).length + B.gates.length := by rw [bitsOf_len]
              rw [hidx, wiresOf_snoc_last]
              simp only [List.map_cons, List.map_nil, GateOp.eval]
              rw [hB.2.2.2.2.2 w0 hw0 z u hu, hB.2.2.2.2.2 w1 hw1 z u hu, add_dotProduct, zmod2_add_decide]
              cases (wiresOf B.gates (bitsOf t z)).getD (B.off w0) false <;>
                cases (wiresOf B.gates (bitsOf t z)).getD (B.off w1) false <;>
                cases decide (dotProduct (B.slope w0) u = 1) <;>
                cases decide (dotProduct (B.slope w1) u = 1) <;> decide)
          exact hwrap_one _ hres.1 rfl hres.2
        · exfalso; have := hshape.1; rw [hg] at this; simp at this
  ·
    rcases hg : g.inputs with _ | ⟨w0, rest⟩
    · simp [hg] at hlen1
    · rcases rest with _ | ⟨_, _⟩
      · have hw0 : w0 < k + t + gs.length := hback w0 (by rw [hg]; simp)
        let gs' := B.gates ++ [⟨.not, [B.off w0]⟩]
        have hleg' : legalGates t gs' :=
          legalGates_snoc hB.2.1 (fun i hi => by simp at hi; subst hi; exact hB.2.2.2.2.1 w0 hw0)
            ⟨by simp, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
        have hcost' : costGates gs' + B.r ≤ costGates (gs ++ [g]) := by
          rw [costGates_snoc_zero B.gates _ (by simp)]; have := hB.2.2.1; omega
        have hres := branch_eval_add_gate hleg hB gs' [⟨.not, [B.off w0]⟩] rfl hleg' hcost'
          (t + B.gates.length) (by simp [gs']) (B.slope w0) (fun z u hu => by
            rw [hop, hg]
            have hidx : t + B.gates.length = (bitsOf t z).length + B.gates.length := by rw [bitsOf_len]
            rw [hidx, wiresOf_snoc_last]
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.headD_cons]
            rw [hB.2.2.2.2.2 w0 hw0 z u hu]
            cases (wiresOf B.gates (bitsOf t z)).getD (B.off w0) false <;>
              cases decide (dotProduct (B.slope w0) u = 1) <;> decide)
        exact hwrap_one _ hres.1 rfl hres.2
      · simp [hg] at hlen1

lemma build_branch_list (k t : ℕ) (gs : List Gate) (hleg : legalGates (k + t) gs) :
    ∃ L : List (Branch k t),
      0 < L.length ∧
      (∀ B ∈ L, ValidBranch gs B) ∧
      ∀ (z : Fin t → F2) (x : Fin k → F2),
        ∃! idx : Fin L.length, x - (L.get idx).pos z ∈ (L.get idx).U := by
  induction gs using List.reverseRecOn with
  | nil =>
    let g0 : List Gate := [⟨.or, []⟩]
    let B0 : Branch k t :=
      ⟨0, ⊤, g0, fun _ => t,
        fun w => if w < k then t else w - k,
        fun w => if hw : w < k then Pi.single ⟨w, hw⟩ (1 : F2) else 0⟩
    have hleg0 : legalGates t g0 := by
      have hnil : legalGates t [] := ⟨fun j hj => by simp at hj, fun h hh => by simp at hh⟩
      exact legalGates_snoc hnil (by simp) ⟨by simp, Or.inr (Or.inl rfl)⟩
    have hg0_val : ∀ z : Fin t → F2, (wiresOf g0 (bitsOf t z)).getD t false = false := by
      intro z
      have h1 := wiresOf_snoc_last_eq ([] : List Gate) ⟨.or, []⟩ (bitsOf t z) (bitsOf_len t z)
      simpa [g0, GateOp.eval] using h1
    have hpos0 : ∀ z : Fin t → F2, B0.pos z = 0 := by
      intro z; funext j
      simp only [branch_gates_mk, branch_tap_mk, Branch.pos, B0, Pi.zero_apply, hg0_val z]
      rfl
    have hvalid0 : ValidBranch [] B0 := by
      refine ⟨?_, hleg0, ?_, fun _ => by simp [branch_gates_mk, branch_tap_mk, B0, g0], ?_, ?_⟩
      · simp [branch_r_mk, branch_U_mk, B0]
      · simp [branch_r_mk, branch_gates_mk, B0, g0, costGates]
      · intro w hw
        simp only [List.length_nil, Nat.add_zero] at hw
        simp only [branch_gates_mk, branch_off_mk, B0, g0, List.length_singleton]
        split_ifs <;> omega
      · intro w hw z u _
        simp only [List.length_nil, Nat.add_zero] at hw
        rw [hpos0 z, zero_add]
        conv_lhs => simp only [branch_r_mk, branch_U_mk, branch_gates_mk, branch_tap_mk, branch_off_mk, branch_slope_mk, wiresOf, Circuit.wires, List.foldl_nil]
        simp only [branch_gates_mk, branch_off_mk, branch_slope_mk, B0]
        by_cases hwk : w < k
        · simp only [hwk, ↓reduceIte, ↓reduceDIte]
          have h1 : (bitsOf k u ++ bitsOf t z).getD w false = decide (u ⟨w, hwk⟩ = 1) := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [bitsOf_len]; exact hwk)]
            exact bitsOf_getD k u ⟨w, hwk⟩
          rw [h1, hg0_val z]
          simp
        · simp only [hwk, ↓reduceIte, ↓reduceDIte]
          have h1 : (bitsOf k u ++ bitsOf t z).getD w false = (bitsOf t z).getD (w - k) false := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [bitsOf_len]; omega),
                bitsOf_len, List.getD_eq_getElem?_getD]
          have h2 : (wiresOf g0 (bitsOf t z)).getD (w - k) false = (bitsOf t z).getD (w - k) false :=
            wiresOf_getD_lt g0 (bitsOf t z) (by rw [bitsOf_len]; omega)
          rw [h1, h2]; simp
    refine ⟨[B0], by simp, fun b hb => by simp at hb; subst hb; exact hvalid0, fun z x => ?_⟩
    exact ⟨⟨0, by simp⟩, by simp [branch_r_mk, branch_U_mk, branch_gates_mk, branch_tap_mk, branch_off_mk, branch_slope_mk, B0], fun idx _ => Fin.ext (by have := idx.isLt; simp only [branch_r_mk, branch_U_mk, branch_gates_mk, branch_tap_mk, branch_off_mk, branch_slope_mk, List.length_singleton] at this; change idx.val = 0; omega)⟩
  | append_singleton gs g ih =>
    have hpre := legalGates_prefix hleg
    rcases ih hpre.1 with ⟨L, hLpos, hLval, hLpart⟩
    have hstep_all : ∀ idx : Fin L.length, ∃ Lc : List (Branch k t),
        (∀ B' ∈ Lc, ValidBranch (gs ++ [g]) B') ∧
        ∀ (z : Fin t → F2) (x : Fin k → F2),
          (x - (L.get idx).pos z ∈ (L.get idx).U → ∃! j : Fin Lc.length, x - (Lc.get j).pos z ∈ (Lc.get j).U) ∧
          (x - (L.get idx).pos z ∉ (L.get idx).U → ∀ j : Fin Lc.length, x - (Lc.get j).pos z ∉ (Lc.get j).U) :=
      fun idx => step_single_branch (L.get idx) hleg (hLval _ (List.get_mem L idx))
    let children : Fin L.length → List (Branch k t) := fun idx => (hstep_all idx).choose
    have hchildren_spec : ∀ idx : Fin L.length,
        (∀ B' ∈ children idx, ValidBranch (gs ++ [g]) B') ∧
        ∀ (z : Fin t → F2) (x : Fin k → F2),
          (x - (L.get idx).pos z ∈ (L.get idx).U →
            ∃! j : Fin (children idx).length, x - ((children idx).get j).pos z ∈ ((children idx).get j).U) ∧
          (x - (L.get idx).pos z ∉ (L.get idx).U →
            ∀ j : Fin (children idx).length, x - ((children idx).get j).pos z ∉ ((children idx).get j).U) :=
      fun idx => (hstep_all idx).choose_spec
    let L' : List (Branch k t) := (List.finRange L.length).flatMap children
    have hpart_L' : ∀ (z : Fin t → F2) (x : Fin k → F2),
        ∃! idx' : Fin L'.length, x - (L'.get idx').pos z ∈ (L'.get idx').U := by
      intro z x
      have hflat_bij : ∀ (ms : List (Fin L.length)),
          (∀ a ∈ ms, ∀ b ∈ ms, a = b → True) →
          ms.Nodup →
          ∀ (p : Branch k t → Prop),
            (∃ idx ∈ ms, (∃! j : Fin (children idx).length, p ((children idx).get j)) ∧
              ∀ idx2 ∈ ms, idx2 ≠ idx → ∀ j : Fin (children idx2).length, ¬ p ((children idx2).get j)) →
            ∃! q : Fin (ms.flatMap children).length, p ((ms.flatMap children).get q) := by
        intro ms _ hnd p
        induction ms with
        | nil => rintro ⟨_, h, _⟩; simp at h
        | cons a ms ihms =>
          rintro ⟨idx, hidx, huniq, hrest⟩
          rw [List.nodup_cons] at hnd
          change ∃! q : Fin (children a ++ ms.flatMap children).length, p ((children a ++ ms.flatMap children).get q)
          rcases List.mem_cons.mp hidx with rfl | hmem
          · rcases huniq with ⟨j0, hj0, hj0u⟩
            refine ⟨⟨j0.val, by simp only [List.length_append]; omega⟩, ?_, ?_⟩
            · dsimp only
              rw [List.get_eq_getElem, List.getElem_append_left j0.isLt]
              exact hj0
            · intro q hq
              by_cases hql : q.val < (children idx).length
              · have hq' : p ((children idx).get ⟨q.val, hql⟩) := by
                  simpa [List.get_eq_getElem, List.getElem_append_left hql] using hq
                have := hj0u ⟨q.val, hql⟩ hq'
                exact Fin.ext (by simpa using congrArg Fin.val this)
              · exfalso
                have hqr : q.val - (children idx).length < (ms.flatMap children).length := by
                  have := q.isLt; simp only [List.length_append] at this; omega
                have hq' : p ((ms.flatMap children).get ⟨q.val - (children idx).length, hqr⟩) := by
                  simpa [List.get_eq_getElem, List.getElem_append_right (by omega : (children idx).length ≤ q.val)] using hq
                have hmem_b : (ms.flatMap children).get ⟨q.val - (children idx).length, hqr⟩ ∈ ms.flatMap children :=
                  List.get_mem _ _
                rcases List.mem_flatMap.mp hmem_b with ⟨idx2, hidx2, hb2⟩
                rcases List.mem_iff_get.mp hb2 with ⟨j2, hj2⟩
                have hne2 : idx2 ≠ idx := fun heq => hnd.1 (heq ▸ hidx2)
                exact hrest idx2 (List.mem_cons_of_mem idx hidx2) hne2 j2 (hj2.symm ▸ hq')
          · have hih := ihms (fun _ _ _ _ _ => trivial) hnd.2 ⟨idx, hmem, huniq, fun idx2 hi2 hne2 => hrest idx2 (List.mem_cons_of_mem a hi2) hne2⟩
            rcases hih with ⟨q0, hq0, hq0u⟩
            refine ⟨⟨(children a).length + q0.val, by simp only [List.length_append]; omega⟩, ?_, ?_⟩
            · simp only [List.get_eq_getElem, List.getElem_append_right (by omega : (children a).length ≤ (children a).length + q0.val),
                Nat.add_sub_cancel_left]
              exact hq0
            · intro q hq
              by_cases hql : q.val < (children a).length
              · exfalso
                have hq' : p ((children a).get ⟨q.val, hql⟩) := by
                  simpa [List.get_eq_getElem, List.getElem_append_left hql] using hq
                have hne : a ≠ idx := fun heq => hnd.1 (heq ▸ hmem)
                exact hrest a (List.mem_cons_self) hne ⟨q.val, hql⟩ hq'
              · have hqr : q.val - (children a).length < (ms.flatMap children).length := by
                  have := q.isLt; simp only [List.length_append] at this; omega
                have hq' : p ((ms.flatMap children).get ⟨q.val - (children a).length, hqr⟩) := by
                  simpa [List.get_eq_getElem, List.getElem_append_right (by omega : (children a).length ≤ q.val)] using hq
                have heq := hq0u ⟨q.val - (children a).length, hqr⟩ hq'
                apply Fin.ext
                have := congrArg Fin.val heq
                dsimp at this ⊢; omega
      rcases hLpart z x with ⟨idx0, hidx0, hidx0u⟩
      apply hflat_bij (List.finRange L.length) (fun _ _ _ _ _ => trivial) (List.nodup_finRange L.length)
        (fun B => x - B.pos z ∈ B.U)
      refine ⟨idx0, List.mem_finRange idx0, ((hchildren_spec idx0).2 z x).1 hidx0, ?_⟩
      intro idx2 _ hne2
      have hnot2 : x - (L.get idx2).pos z ∉ (L.get idx2).U := fun hm => hne2 (hidx0u idx2 hm)
      exact ((hchildren_spec idx2).2 z x).2 hnot2
    have hL'pos : 0 < L'.length := by
      rcases hpart_L' 0 0 with ⟨idx0, _, _⟩
      exact Nat.pos_of_ne_zero (fun h0 => by have := idx0.isLt; omega)
    refine ⟨L', hL'pos, ?_, hpart_L'⟩
    intro B' hB'
    rcases List.mem_flatMap.mp hB' with ⟨idx, _, hmem⟩
    exact (hchildren_spec idx).1 B' hmem


open Classical

lemma vec_eq_sum_single {k : ℕ} (v : Fin k → F2) :
    v = ∑ i : Fin k, v i • Pi.single i (1 : F2) := by
  funext j
  simp [Finset.sum_apply, Pi.single_apply]

lemma decomp_835 (k t : ℕ) (C : Circuit) (hC : legalGates (k + t) C.gates) :
    ∃ (N : ℕ) (r : Fin N → ℕ) (U : Fin N → Submodule F2 (Fin k → F2)) (a : Fin N → (Fin k → F2))
      (D : Fin N → Circuit) (tap : Fin N → Fin k → ℕ),
      let pos := fun (i : Fin N) (z : Fin t → F2) (j : Fin k) =>
        if ((D i).wires (bitsOf t z)).getD (tap i j) false then (1 : F2) else 0
      0 < N ∧ (∀ i, Module.finrank F2 (U i) + r i = k ∧ legalGates t (D i).gates ∧
        costGates (D i).gates + r i ≤ costGates C.gates ∧ (D i).output < t + (D i).size ∧
        ∀ j, tap i j < t + (D i).size) ∧
      (∀ (z : Fin t → F2) (x : Fin k → F2), ∃! i : Fin N, x - pos i z ∈ U i) ∧
      ∀ (i : Fin N) (z : Fin t → F2) (u : Fin k → F2), u ∈ U i →
        C.eval (bitsOf k (pos i z + u) ++ bitsOf t z) =
          Bool.xor ((D i).eval (bitsOf t z)) (decide (dotProduct (a i) u = 1)) := by
  rcases build_branch_list k t C.gates hC with ⟨L, hLpos, hLval, hLpart⟩
  by_cases hout : C.output < k + t + C.gates.length
  · refine ⟨L.length,
      fun i => (L.get i).r,
      fun i => (L.get i).U,
      fun i => (L.get i).slope C.output,
      fun i => ⟨(L.get i).gates, (L.get i).off C.output⟩,
      fun i => (L.get i).tap,
      hLpos, ?_, ?_, ?_⟩
    · intro i
      have hBi := hLval (L.get i) (List.get_mem L i)
      exact ⟨hBi.1, hBi.2.1, hBi.2.2.1, hBi.2.2.2.2.1 C.output hout, hBi.2.2.2.1⟩
    · intro z x
      exact hLpart z x
    · intro i z u hu
      have hBi := hLval (L.get i) (List.get_mem L i)
      exact hBi.2.2.2.2.2 C.output hout z u hu
  · refine ⟨L.length,
      fun i => (L.get i).r,
      fun i => (L.get i).U,
      fun _ => 0,
      fun i => ⟨(L.get i).gates ++ [⟨.or, []⟩], t + (L.get i).gates.length⟩,
      fun i => (L.get i).tap,
      hLpos, ?_, ?_, ?_⟩
    · intro i
      have hBi := hLval (L.get i) (List.get_mem L i)
      refine ⟨hBi.1, ?_, ?_, by simp [Circuit.size], ?_⟩
      · exact legalGates_snoc hBi.2.1 (by simp) ⟨by simp, Or.inr (Or.inl rfl)⟩
      · have hc0 := costGates_snoc_zero (L.get i).gates ⟨.or, []⟩ (by simp)
        have := hBi.2.2.1
        change costGates ((L.get i).gates ++ [⟨.or, []⟩]) + (L.get i).r ≤ costGates C.gates
        omega
      · intro j
        simp only [Circuit.size, List.length_append, List.length_singleton]
        have := hBi.2.2.2.1 j; omega
    · intro z x
      have hpeq : ∀ i : Fin L.length,
          (fun j : Fin k => if (Circuit.wires ⟨(L.get i).gates ++ [⟨.or, []⟩], t + (L.get i).gates.length⟩ (bitsOf t z)).getD ((L.get i).tap j) false then (1 : F2) else 0) =
          (L.get i).pos z := by
        intro i; funext j
        have hBi := hLval (L.get i) (List.get_mem L i)
        change (if (wiresOf ((L.get i).gates ++ [⟨.or, []⟩]) (bitsOf t z)).getD ((L.get i).tap j) false then (1 : F2) else 0) = _
        rw [wiresOf_append_getD_lt (L.get i).gates [⟨.or, []⟩] _
          (by rw [bitsOf_len]; exact hBi.2.2.2.1 j)]
        rfl
      have hconv : (fun i : Fin L.length => x - (fun j : Fin k => if (Circuit.wires ⟨(L.get i).gates ++ [⟨.or, []⟩], t + (L.get i).gates.length⟩ (bitsOf t z)).getD ((L.get i).tap j) false then (1 : F2) else 0) ∈ (L.get i).U) =
          (fun i : Fin L.length => x - (L.get i).pos z ∈ (L.get i).U) := by
        funext i; rw [hpeq i]
      exact (congrArg (fun P => ∃! i : Fin L.length, P i) hconv).mpr (hLpart z x)
    · intro i z u _
      have hlhs : ∀ v : Fin k → F2, C.eval (bitsOf k v ++ bitsOf t z) = false := by
        intro v
        have hclen : (C.wires (bitsOf k v ++ bitsOf t z)).length = k + t + C.gates.length := by
          have h := wiresOf_len C.gates (bitsOf k v ++ bitsOf t z)
          simp only [List.length_append, bitsOf_len] at h
          exact h
        unfold Circuit.eval
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
        rfl
      have hrhs : (Circuit.mk ((L.get i).gates ++ [⟨.or, []⟩]) (t + (L.get i).gates.length)).eval (bitsOf t z) = false := by
        unfold Circuit.eval
        change (wiresOf ((L.get i).gates ++ [⟨.or, []⟩]) (bitsOf t z)).getD (t + (L.get i).gates.length) false = false
        rw [wiresOf_snoc_last_eq (L.get i).gates ⟨.or, []⟩ (bitsOf t z) (bitsOf_len t z)]
        simp [GateOp.eval]
      rw [hlhs, hrhs]
      simp

def signBool (b : Bool) : ℤ := if b then -1 else 1

lemma signBool_xor (a b : Bool) : signBool (Bool.xor a b) = signBool a * signBool b := by
  cases a <;> cases b <;> rfl

lemma agree_eq_sign (b1 b2 b3 : Bool) :
    (if b1 = Bool.xor b2 b3 then (1 : ℤ) else -1) = signBool (Bool.xor b1 b2) * signBool b3 := by
  cases b1 <;> cases b2 <;> cases b3 <;> rfl

lemma eq_f2_sign (a b : F2) :
    (if a = b then (1 : ℤ) else -1) = signBool (decide (a = 1)) * signBool (decide (b = 1)) := by
  fin_cases a <;> fin_cases b <;> decide

lemma signBool_abs_one (b : Bool) : |signBool b| = 1 := by
  cases b <;> simp [signBool]

lemma card_submodule_zmod2 {k : ℕ} (U : Submodule F2 (Fin k → F2)) :
    Fintype.card U = 2 ^ Module.finrank F2 U := by
  let b := Module.finBasis F2 U
  rw [Fintype.card_congr b.equivFun.toEquiv]
  simp [ZMod.card]

def orthoComp {k : ℕ} (U : Submodule F2 (Fin k → F2)) : Submodule F2 (Fin k → F2) :=
  { carrier := {w | ∀ u ∈ U, dotProduct w u = 0},
    zero_mem' := fun u _ => by simp, smul_mem' := fun c {a} ha u hu => by rw [smul_dotProduct, ha u hu, smul_zero], add_mem' := fun {a b} ha hb u hu => by rw [add_dotProduct, ha u hu, hb u hu, add_zero] }

lemma mem_orthoComp {k : ℕ} (U : Submodule F2 (Fin k → F2)) (w : Fin k → F2) :
    w ∈ orthoComp U ↔ ∀ u ∈ U, dotProduct w u = 0 := Iff.rfl

lemma finrank_orthoComp {k : ℕ} (U : Submodule F2 (Fin k → F2)) :
    Module.finrank F2 (orthoComp U) + Module.finrank F2 U = k := by
  let b := Module.finBasis F2 U
  let Φ : (Fin k → F2) →ₗ[F2] (Fin (Module.finrank F2 U) → F2) :=
    { toFun := fun w i => dotProduct w (b i).val
      map_add' := fun x y => by funext i; exact add_dotProduct x y (b i).val
      map_smul' := fun c x => by funext i; simp [smul_dotProduct] }
  have hker : LinearMap.ker Φ = orthoComp U := by
    ext w
    simp only [LinearMap.mem_ker, mem_orthoComp]
    constructor
    · intro hw u hu
      have hrep : (⟨u, hu⟩ : U) = ∑ i, b.repr ⟨u, hu⟩ i • b i := (b.sum_repr ⟨u, hu⟩).symm
      have hu_eq : u = ∑ i, b.repr ⟨u, hu⟩ i • (b i).val := by
        have hval := congrArg Subtype.val hrep
        simp only [Submodule.coe_sum, SetLike.val_smul] at hval
        exact hval
      rw [hu_eq, dotProduct_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [dotProduct_smul, smul_eq_mul]
      have hwi : dotProduct w (b i).val = 0 := congrFun hw i
      rw [hwi, mul_zero]
    · intro hw
      funext i
      exact hw (b i).val (b i).property
  have hsurj : LinearMap.range Φ = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro target
    let f : U →ₗ[F2] F2 :=
      { toFun := fun u => ∑ i, target i * b.repr u i
        map_add' := fun x y => by simp only [map_add, Finsupp.coe_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]
        map_smul' := fun c x => by
          simp only [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => by ring }
    obtain ⟨V', hcompl⟩ := Submodule.exists_isCompl U
    let π : (Fin k → F2) →ₗ[F2] U := Submodule.linearProjOfIsCompl U V' hcompl
    let g : (Fin k → F2) →ₗ[F2] F2 := f.comp π
    let w : Fin k → F2 := fun j => g (Pi.single j 1)
    refine ⟨w, ?_⟩
    funext i
    have hgx : ∀ x : Fin k → F2, dotProduct w x = g x := by
      intro x
      conv_rhs => rw [vec_eq_sum_single x]
      rw [map_sum]
      simp only [dotProduct, map_smul, smul_eq_mul, w]
      refine Finset.sum_congr rfl fun j _ => by ring
    change dotProduct w (b i).val = target i
    rw [hgx (b i).val]
    have hpi : π (b i).val = b i := Submodule.linearProjOfIsCompl_apply_left hcompl (b i)
    simp only [g, LinearMap.comp_apply, hpi, f, LinearMap.coe_mk, AddHom.coe_mk, Module.Basis.repr_self]
    simp [Finsupp.single_apply]
  have hrk := LinearMap.finrank_range_add_finrank_ker Φ
  rw [hsurj, hker, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at hrk
  omega

lemma sum_sign_dot_submodule {k : ℕ} (U : Submodule F2 (Fin k → F2)) (w : Fin k → F2) :
    (∑ u : U, signBool (decide (dotProduct w u.val = 1))) =
      if w ∈ orthoComp U then (2 : ℤ) ^ Module.finrank F2 U else 0 := by
  by_cases hw : w ∈ orthoComp U
  · simp only [hw, ↓reduceIte]
    have hterm : ∀ u : U, signBool (decide (dotProduct w u.val = 1)) = 1 := by
      intro u
      rw [hw u.val u.property]
      rfl
    simp only [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      card_submodule_zmod2, Nat.cast_pow, Nat.cast_ofNat]
  · simp only [hw, ↓reduceIte]
    have hex : ∃ u0 ∈ U, dotProduct w u0 = 1 := by
      by_contra hnot
      apply hw
      intro u hu
      rcases zmod2_cases (dotProduct w u) with h0 | h1
      · exact h0
      · exact absurd ⟨u, hu, h1⟩ hnot
    rcases hex with ⟨u0, hu0, hdot⟩
    let e : U ≃ U :=
      { toFun := fun u => u + ⟨u0, hu0⟩
        invFun := fun u => u + ⟨u0, hu0⟩
        left_inv := fun u => Subtype.ext (by
          show u.val + u0 + u0 = u.val
          rw [add_assoc, zmod2_vec_add_self, add_zero])
        right_inv := fun u => Subtype.ext (by
          show u.val + u0 + u0 = u.val
          rw [add_assoc, zmod2_vec_add_self, add_zero]) }
    set S := ∑ u : U, signBool (decide (dotProduct w u.val = 1))
    have hS : S = -S := by
      calc S = ∑ u : U, signBool (decide (dotProduct w (e u).val = 1)) :=
            (Equiv.sum_comp e (fun u : U => signBool (decide (dotProduct w u.val = 1)))).symm
        _ = ∑ u : U, -signBool (decide (dotProduct w u.val = 1)) := by
            refine Finset.sum_congr rfl fun u _ => ?_
            show signBool (decide (dotProduct w (u.val + u0) = 1)) = _
            rw [dotProduct_add, hdot, zmod2_add_decide]
            cases decide (dotProduct w u.val = 1) <;> rfl
        _ = -S := by rw [Finset.sum_neg_distrib]
    omega

lemma sum_sign_dot_univ {k : ℕ} (w : Fin k → F2) (hw : w ≠ 0) :
    (∑ x : Fin k → F2, signBool (decide (dotProduct w x = 1))) = 0 := by
  have hex : ∃ j : Fin k, w j = 1 := by
    by_contra hnot; push Not at hnot
    apply hw; funext j
    rcases zmod2_cases (w j) with h0 | h1
    · exact h0
    · exact absurd h1 (hnot j)
  rcases hex with ⟨j, hj⟩
  let u0 : Fin k → F2 := Pi.single j 1
  have hdot : dotProduct w u0 = 1 := by
    simp [u0, dotProduct_single, hj]
  let e : (Fin k → F2) ≃ (Fin k → F2) :=
    { toFun := fun x => x + u0
      invFun := fun x => x + u0
      left_inv := fun x => by dsimp only; rw [add_assoc, zmod2_vec_add_self, add_zero]
      right_inv := fun x => by dsimp only; rw [add_assoc, zmod2_vec_add_self, add_zero] }
  set S := ∑ x : Fin k → F2, signBool (decide (dotProduct w x = 1))
  have hS : S = -S := by
    calc S = ∑ x : Fin k → F2, signBool (decide (dotProduct w (e x) = 1)) :=
          (Equiv.sum_comp e (fun x => signBool (decide (dotProduct w x = 1)))).symm
      _ = ∑ x : Fin k → F2, -signBool (decide (dotProduct w x = 1)) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          show signBool (decide (dotProduct w (x + u0) = 1)) = _
          rw [dotProduct_add, hdot, zmod2_add_decide]
          cases decide (dotProduct w x = 1) <;> rfl
      _ = -S := by rw [Finset.sum_neg_distrib]
  omega

lemma cost_zero_affine {k : ℕ} (gs : List Gate) (hleg : legalGates k gs) (hcost : costGates gs = 0) :
    ∀ w < k + gs.length, ∃ (lin : Fin k → F2) (c : F2), ∀ y : Fin k → F2,
      (wiresOf gs (bitsOf k y)).getD w false = decide (dotProduct lin y + c = 1) := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro w hw
    simp only [List.length_nil, Nat.add_zero] at hw
    refine ⟨Pi.single ⟨w, hw⟩ 1, 0, fun y => ?_⟩
    change (bitsOf k y).getD (⟨w, hw⟩ : Fin k).val false = _
    rw [bitsOf_getD, single_dotProduct, one_mul, add_zero]
  | append_singleton gs g ih =>
    have hpre := legalGates_prefix hleg
    have hcost_app : costGates gs + costGates [g] = 0 := by
      rw [← costGates_append]; exact hcost
    have hcost_gs : costGates gs = 0 := by omega
    have hnot_nl : ¬ ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) := by
      intro hnl
      have h1 : costGates (gs ++ [g]) = costGates gs + 1 := costGates_snoc_one gs g hnl
      omega
    have hih := ih hpre.1 hcost_gs
    intro w hw
    simp only [List.length_append, List.length_singleton] at hw
    by_cases hlt : w < k + gs.length
    · obtain ⟨lin, c, hlin⟩ := hih w hlt
      refine ⟨lin, c, fun y => ?_⟩
      rw [wiresOf_append_getD_lt gs [g] (bitsOf k y) (by rw [bitsOf_len]; exact hlt)]
      exact hlin y
    · have hweq : w = k + gs.length := by omega
      subst hweq
      have hback := hpre.2.1
      have hshape := hpre.2.2
      have eval_snoc : ∀ y : Fin k → F2,
          (wiresOf (gs ++ [g]) (bitsOf k y)).getD (k + gs.length) false =
            g.op.eval (g.inputs.map fun i => (wiresOf gs (bitsOf k y)).getD i false) :=
        fun y => wiresOf_snoc_last_eq gs g (bitsOf k y) (bitsOf_len k y)
      rcases hshape.2 with hop | hop | hop | ⟨hop, hlen1⟩
      · rcases hg : g.inputs with _ | ⟨w0, rest⟩
        · refine ⟨0, 1, fun y => ?_⟩
          rw [eval_snoc y, hop, hg]; simp [GateOp.eval]
        · rcases rest with _ | ⟨w1, rest2⟩
          · obtain ⟨lin, c, hlin⟩ := hih w0 (hback w0 (by rw [hg]; simp))
            refine ⟨lin, c, fun y => ?_⟩
            rw [eval_snoc y, hop, hg]
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
            exact hlin y
          · rcases rest2 with _ | ⟨_, _⟩
            · exfalso; exact hnot_nl ⟨Or.inl hop, by rw [hg]; rfl⟩
            · exfalso; have := hshape.1; rw [hg] at this; simp at this
      · rcases hg : g.inputs with _ | ⟨w0, rest⟩
        · refine ⟨0, 0, fun y => ?_⟩
          rw [eval_snoc y, hop, hg]; simp [GateOp.eval]
        · rcases rest with _ | ⟨w1, rest2⟩
          · obtain ⟨lin, c, hlin⟩ := hih w0 (hback w0 (by rw [hg]; simp))
            refine ⟨lin, c, fun y => ?_⟩
            rw [eval_snoc y, hop, hg]
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
            exact hlin y
          · rcases rest2 with _ | ⟨_, _⟩
            · exfalso; exact hnot_nl ⟨Or.inr hop, by rw [hg]; rfl⟩
            · exfalso; have := hshape.1; rw [hg] at this; simp at this
      · rcases hg : g.inputs with _ | ⟨w0, rest⟩
        · refine ⟨0, 1, fun y => ?_⟩
          rw [eval_snoc y, hop, hg]; simp [GateOp.eval]
        · rcases rest with _ | ⟨w1, rest2⟩
          · obtain ⟨lin, c, hlin⟩ := hih w0 (hback w0 (by rw [hg]; simp))
            refine ⟨lin, c + 1, fun y => ?_⟩
            rw [eval_snoc y, hop, hg]
            simp only [List.map_cons, List.map_nil, hlin y, GateOp.eval]
            rcases zmod2_cases (dotProduct lin y + c) with h | h <;> rw [← add_assoc, h] <;> decide
          · rcases rest2 with _ | ⟨_, _⟩
            · obtain ⟨lin0, c0, hlin0⟩ := hih w0 (hback w0 (by rw [hg]; simp))
              obtain ⟨lin1, c1, hlin1⟩ := hih w1 (hback w1 (by rw [hg]; simp))
              refine ⟨lin0 + lin1, c0 + c1 + 1, fun y => ?_⟩
              rw [eval_snoc y, hop, hg]
              simp only [List.map_cons, List.map_nil, hlin0 y, hlin1 y, GateOp.eval, add_dotProduct]
              have hrw : dotProduct lin0 y + dotProduct lin1 y + (c0 + c1 + 1) =
                  (dotProduct lin0 y + c0) + (dotProduct lin1 y + c1) + 1 := by ring
              rw [hrw]
              rcases zmod2_cases (dotProduct lin0 y + c0) with h0 | h0 <;>
                rcases zmod2_cases (dotProduct lin1 y + c1) with h1 | h1 <;>
                rw [h0, h1] <;> decide
            · exfalso; have := hshape.1; rw [hg] at this; simp at this
      · rcases hg : g.inputs with _ | ⟨w0, rest⟩
        · simp [hg] at hlen1
        · rcases rest with _ | ⟨_, _⟩
          · obtain ⟨lin, c, hlin⟩ := hih w0 (hback w0 (by rw [hg]; simp))
            refine ⟨lin, c + 1, fun y => ?_⟩
            rw [eval_snoc y, hop, hg]
            simp only [List.map_cons, List.map_nil, hlin y, GateOp.eval, List.headD_cons]
            rcases zmod2_cases (dotProduct lin y + c) with h | h <;> rw [← add_assoc, h] <;> decide
          · simp [hg] at hlen1

def isQuad {s : ℕ} (q : (Fin s → F2) → F2) : Prop :=
  ∃ (b : F2) (a : Fin s → F2) (M : Fin s → Fin s → F2), ∀ v,
    q v = b + dotProduct a v + ∑ i, ∑ j, M i j * v i * v j

lemma isQuad_const {s : ℕ} (b : F2) : isQuad (s := s) (fun _ => b) :=
  ⟨b, 0, fun _ _ => 0, fun _ => by simp⟩

lemma isQuad_affine {s : ℕ} (a : Fin s → F2) (b : F2) :
    isQuad (s := s) (fun v => dotProduct a v + b) :=
  ⟨b, a, fun _ _ => 0, fun v => by simp [add_comm]⟩

lemma isQuad_add {s : ℕ} {q1 q2 : (Fin s → F2) → F2} (h1 : isQuad q1) (h2 : isQuad q2) :
    isQuad (fun v => q1 v + q2 v) := by
  rcases h1 with ⟨b1, a1, M1, h1⟩
  rcases h2 with ⟨b2, a2, M2, h2⟩
  refine ⟨b1 + b2, a1 + a2, fun i j => M1 i j + M2 i j, fun v => ?_⟩
  dsimp only
  rw [h1 v, h2 v, add_dotProduct]
  have hsum : (∑ i : Fin s, ∑ j : Fin s, (M1 i j + M2 i j) * v i * v j) =
      (∑ i : Fin s, ∑ j : Fin s, M1 i j * v i * v j) +
      (∑ i : Fin s, ∑ j : Fin s, M2 i j * v i * v j) := by
    simp only [add_mul, Finset.sum_add_distrib]
  rw [hsum]; ring

lemma isQuad_mul_affine {s : ℕ} (u1 u2 : Fin s → F2) (c1 c2 : F2) :
    isQuad (fun v => (dotProduct u1 v + c1) * (dotProduct u2 v + c2)) := by
  refine ⟨c1 * c2, c2 • u1 + c1 • u2, fun i j => u1 i * u2 j, fun v => ?_⟩
  dsimp only
  rw [add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  have hprod : dotProduct u1 v * dotProduct u2 v =
      ∑ i : Fin s, ∑ j : Fin s, u1 i * u2 j * v i * v j := by
    simp only [dotProduct, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [← hprod]; ring

lemma isQuad_finset_sum {s : ℕ} {ι : Type*} (S : Finset ι) (f : ι → (Fin s → F2) → F2)
    (hf : ∀ i ∈ S, isQuad (f i)) :
    isQuad (fun v => ∑ i ∈ S, f i v) := by
  induction S using Finset.induction_on with
  | empty => simpa using isQuad_const (s := s) 0
  | @insert a S ha ih =>
    have hfa := hf a (Finset.mem_insert_self a S)
    have hfs := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have heq : (fun v => ∑ i ∈ insert a S, f i v) = (fun v => f a v + ∑ i ∈ S, f i v) := by
      funext v; exact Finset.sum_insert ha
    rw [heq]
    exact isQuad_add hfa hfs

lemma linear_comp_affine {k s : ℕ} (B : (Fin s → F2) →ₗ[F2] (Fin k → F2))
    (a : Fin k → F2) (u : Fin k → F2) (c : F2) :
    ∃ (u' : Fin s → F2) (c' : F2), ∀ v : Fin s → F2,
      dotProduct u (a + B v) + c = dotProduct u' v + c' := by
  refine ⟨fun i => dotProduct u (B (Pi.single i 1)), dotProduct u a + c, fun v => ?_⟩
  rw [dotProduct_add]
  have hBv : dotProduct u (B v) = dotProduct (fun i => dotProduct u (B (Pi.single i 1))) v := by
    conv_lhs => rw [vec_eq_sum_single v, map_sum, dotProduct_sum]
    simp only [dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [hBv]; ring

lemma appendConst_spec (n : ℕ) (gs : List Gate) (b : F2) (hgs : legalGates n gs) :
    let g := if b = 1 then Gate.mk .and [] else Gate.mk .or []
    let gs' := gs ++ [g]
    legalGates n gs' ∧
    costGates gs' = costGates gs ∧
    n + gs.length < n + gs'.length ∧
    ∀ x : List Bool, x.length = n →
      (wiresOf gs' x).getD (n + gs.length) false = decide (b = 1) := by
  intro g gs'
  have hshape : g.inputs.length ≤ 2 ∧
      (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1)) := by
    dsimp only [branch_r_mk, branch_U_mk, branch_gates_mk, branch_tap_mk, branch_off_mk, branch_slope_mk, g]; split_ifs
    · exact ⟨by simp, Or.inl rfl⟩
    · exact ⟨by simp, Or.inr (Or.inl rfl)⟩
  have hback : ∀ i ∈ g.inputs, i < n + gs.length := by
    dsimp only [branch_r_mk, branch_U_mk, branch_gates_mk, branch_tap_mk, branch_off_mk, branch_slope_mk, g]; split_ifs <;> simp
  refine ⟨legalGates_snoc hgs hback hshape, ?_, by simp [gs'], ?_⟩
  · apply costGates_snoc_zero gs g
    dsimp only [branch_r_mk, branch_U_mk, branch_gates_mk, branch_tap_mk, branch_off_mk, branch_slope_mk, g]; split_ifs <;> simp
  · intro x hx
    rw [wiresOf_snoc_last_eq gs g x hx]
    rcases zmod2_cases b with rfl | rfl <;> simp [g, GateOp.eval]

def appendAffineLoop (n : ℕ) (c : Fin n → F2) : (m : ℕ) → m ≤ n → List Gate → ℕ → List Gate × ℕ
  | 0, _, gs, acc => (gs, acc)
  | m + 1, hm, gs, acc =>
    let res := appendAffineLoop n c m (by omega) gs acc
    let gs1 := res.1
    let acc1 := res.2
    if c ⟨m, hm⟩ = 1 then
      (gs1 ++ [⟨.mod 2, [acc1, m]⟩, ⟨.not, [n + gs1.length]⟩], n + gs1.length + 1)
    else (gs1, acc1)

lemma appendAffineLoop_spec (n : ℕ) (c : Fin n → F2) :
    ∀ (m : ℕ) (hm : m ≤ n) (gs : List Gate) (acc : ℕ),
      legalGates n gs → acc < n + gs.length →
      let res := appendAffineLoop n c m hm gs acc
      ∃ ext : List Gate,
        res.1 = gs ++ ext ∧
        legalGates n res.1 ∧
        costGates res.1 = costGates gs ∧
        res.2 < n + res.1.length ∧
        ∀ u : Fin n → F2,
          (wiresOf res.1 (bitsOf n u)).getD res.2 false =
            Bool.xor ((wiresOf gs (bitsOf n u)).getD acc false)
              (decide ((∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < m), c j * u j) = 1)) := by
  intro m
  induction m with
  | zero =>
    intro hm gs acc hleg hacc
    refine ⟨[], by simp [appendAffineLoop], hleg, rfl, hacc, fun u => ?_⟩
    have hemp : Finset.univ.filter (fun j : Fin n => j.val < 0) = ∅ := by ext j; simp
    simp [appendAffineLoop, hemp]
  | succ m ih =>
    intro hm gs acc hleg hacc
    rcases ih (by omega) gs acc hleg hacc with ⟨ext1, h1eq, h1leg, h1cost, h1lt, h1sem⟩
    set gs1 := (appendAffineLoop n c m (by omega) gs acc).1
    set acc1 := (appendAffineLoop n c m (by omega) gs acc).2
    have hsplit : (Finset.univ.filter (fun j : Fin n => j.val < m + 1)) =
        insert ⟨m, hm⟩ (Finset.univ.filter (fun j : Fin n => j.val < m)) := by
      ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
      omega
    have hnotmem : (⟨m, hm⟩ : Fin n) ∉ Finset.univ.filter (fun j : Fin n => j.val < m) := by simp
    by_cases hcm : c ⟨m, hm⟩ = 1
    · have hstep := addXor_step n gs1 acc1 m h1leg h1lt (by omega)
      refine ⟨ext1 ++ [⟨.mod 2, [acc1, m]⟩, ⟨.not, [n + gs1.length]⟩], ?_, ?_, ?_, ?_, ?_⟩
      · simp [appendAffineLoop, hcm, gs1, acc1, h1eq, List.append_assoc]
      · simpa [appendAffineLoop, hcm, gs1, acc1] using hstep.1
      · simpa [appendAffineLoop, hcm, gs1, acc1, h1cost] using hstep.2.1
      · simp only [appendAffineLoop, hcm, ↓reduceIte, List.length_append, List.length_cons, List.length_nil]
        omega
      · intro u
        simp only [appendAffineLoop, hcm, ↓reduceIte]
        change (wiresOf (gs1 ++ [⟨.mod 2, [acc1, m]⟩, ⟨.not, [n + gs1.length]⟩]) (bitsOf n u)).getD (n + gs1.length + 1) false = _
        rw [hstep.2.2.2 (bitsOf n u) (bitsOf_len n u), h1sem u]
        have hm_wire : (wiresOf gs1 (bitsOf n u)).getD m false = decide (u ⟨m, hm⟩ = 1) := by
          rw [wiresOf_getD_lt gs1 (bitsOf n u) (by rw [bitsOf_len]; exact hm)]
          exact bitsOf_getD n u ⟨m, hm⟩
        rw [hm_wire, hsplit, Finset.sum_insert hnotmem, hcm, one_mul, zmod2_add_decide]
        cases (wiresOf gs (bitsOf n u)).getD acc false <;>
          cases decide (u ⟨m, hm⟩ = 1) <;>
          cases decide ((∑ x ∈ Finset.univ.filter (fun j : Fin n => j.val < m), c x * u x) = 1) <;> decide
    · have hcm0 : c ⟨m, hm⟩ = 0 := by
        rcases zmod2_cases (c ⟨m, hm⟩) with h0 | h1
        · exact h0
        · exact absurd h1 hcm
      refine ⟨ext1, ?_, ?_, ?_, ?_, ?_⟩
      · simp [appendAffineLoop, hcm, gs1, h1eq]
      · simpa [appendAffineLoop, hcm, gs1] using h1leg
      · simpa [appendAffineLoop, hcm, gs1] using h1cost
      · simpa [appendAffineLoop, hcm, gs1, acc1] using h1lt
      · intro u
        simp only [appendAffineLoop, hcm, ↓reduceIte]
        rw [h1sem u, hsplit, Finset.sum_insert hnotmem, hcm0, zero_mul, zero_add]

def appendAffine (n : ℕ) (gs : List Gate) (c : Fin n → F2) (b : F2) : List Gate × ℕ :=
  let g0 := if b = 1 then Gate.mk .and [] else Gate.mk .or []
  appendAffineLoop n c n (le_refl n) (gs ++ [g0]) (n + gs.length)

lemma appendAffine_spec (n : ℕ) (gs : List Gate) (c : Fin n → F2) (b : F2) (hgs : legalGates n gs) :
    let res := appendAffine n gs c b
    ∃ ext : List Gate,
      res.1 = gs ++ ext ∧
      legalGates n res.1 ∧
      costGates res.1 = costGates gs ∧
      res.2 < n + res.1.length ∧
      ∀ u : Fin n → F2,
        (wiresOf res.1 (bitsOf n u)).getD res.2 false = decide (dotProduct c u + b = 1) := by
  have hc := appendConst_spec n gs b hgs
  let g0 := if b = 1 then Gate.mk .and [] else Gate.mk .or []
  rcases appendAffineLoop_spec n c n (le_refl n) (gs ++ [g0]) (n + gs.length) hc.1 hc.2.2.1 with
    ⟨ext1, h1eq, h1leg, h1cost, h1lt, h1sem⟩
  refine ⟨[g0] ++ ext1, ?_, h1leg, ?_, h1lt, ?_⟩
  · simpa [appendAffine, g0, List.append_assoc] using h1eq
  · dsimp only [branch_r_mk, branch_U_mk, branch_gates_mk, branch_tap_mk, branch_off_mk, branch_slope_mk, appendAffine]
    rw [h1cost, hc.2.1]
  · intro u
    change (wiresOf (appendAffineLoop n c n (le_refl n) (gs ++ [g0]) (n + gs.length)).1 (bitsOf n u)).getD
        (appendAffineLoop n c n (le_refl n) (gs ++ [g0]) (n + gs.length)).2 false = _
    rw [h1sem u, hc.2.2.2 (bitsOf n u) (bitsOf_len n u)]
    have huniv : Finset.univ.filter (fun j : Fin n => j.val < n) = Finset.univ := by
      ext j; simp [j.isLt]
    rw [huniv]
    change Bool.xor (decide (b = 1)) (decide (dotProduct c u = 1)) = _
    rw [zmod2_add_decide, Bool.xor_comm]

def appendSumProdsLoop (n s : ℕ) (cA cB : Fin s → Fin n → F2) (bA bB : Fin s → F2) :
    (m : ℕ) → m ≤ s → List Gate → ℕ → List Gate × ℕ
  | 0, _, gs, acc => (gs, acc)
  | m + 1, hm, gs, acc =>
    let res1 := appendSumProdsLoop n s cA cB bA bB m (by omega) gs acc
    let gs1 := res1.1
    let acc1 := res1.2
    let resA := appendAffine n gs1 (cA ⟨m, hm⟩) (bA ⟨m, hm⟩)
    let gs2 := resA.1
    let wA := resA.2
    let resB := appendAffine n gs2 (cB ⟨m, hm⟩) (bB ⟨m, hm⟩)
    let gs3 := resB.1
    let wB := resB.2
    let gs4 := gs3 ++ [⟨.and, [wA, wB]⟩]
    let wP := n + gs3.length
    (gs4 ++ [⟨.mod 2, [acc1, wP]⟩, ⟨.not, [n + gs4.length]⟩], n + gs4.length + 1)

lemma appendSumProdsLoop_spec (n s : ℕ) (cA cB : Fin s → Fin n → F2) (bA bB : Fin s → F2) :
    ∀ (m : ℕ) (hm : m ≤ s) (gs : List Gate) (acc : ℕ),
      legalGates n gs → acc < n + gs.length →
      let res := appendSumProdsLoop n s cA cB bA bB m hm gs acc
      ∃ ext : List Gate,
        res.1 = gs ++ ext ∧
        legalGates n res.1 ∧
        costGates res.1 = costGates gs + m ∧
        res.2 < n + res.1.length ∧
        ∀ u : Fin n → F2,
          (wiresOf res.1 (bitsOf n u)).getD res.2 false =
            Bool.xor ((wiresOf gs (bitsOf n u)).getD acc false)
              (decide ((∑ i ∈ Finset.univ.filter (fun i : Fin s => i.val < m),
                (dotProduct (cA i) u + bA i) * (dotProduct (cB i) u + bB i)) = 1)) := by
  intro m
  induction m with
  | zero =>
    intro hm gs acc hleg hacc
    refine ⟨[], by simp [branch_r_mk, branch_U_mk, branch_gates_mk, branch_tap_mk, branch_off_mk, branch_slope_mk, appendSumProdsLoop], hleg, by simp [branch_r_mk, branch_U_mk, branch_gates_mk, branch_tap_mk, branch_off_mk, branch_slope_mk, appendSumProdsLoop], hacc, fun u => ?_⟩
    have hemp : Finset.univ.filter (fun i : Fin s => i.val < 0) = ∅ := by ext i; simp
    simp [appendSumProdsLoop, hemp]
  | succ m ih =>
    intro hm gs acc hleg hacc
    rcases ih (by omega) gs acc hleg hacc with ⟨ext1, h1eq, h1leg, h1cost, h1lt, h1sem⟩
    set res1 := appendSumProdsLoop n s cA cB bA bB m (by omega) gs acc
    set gs1 := res1.1
    set acc1 := res1.2
    rcases appendAffine_spec n gs1 (cA ⟨m, hm⟩) (bA ⟨m, hm⟩) h1leg with ⟨extA, hAeq, hAleg, hAcost, hAlt, hAsem⟩
    set resA := appendAffine n gs1 (cA ⟨m, hm⟩) (bA ⟨m, hm⟩)
    set gs2 := resA.1
    set wA := resA.2
    rcases appendAffine_spec n gs2 (cB ⟨m, hm⟩) (bB ⟨m, hm⟩) hAleg with ⟨extB, hBeq, hBleg, hBcost, hBlt, hBsem⟩
    set resB := appendAffine n gs2 (cB ⟨m, hm⟩) (bB ⟨m, hm⟩)
    set gs3 := resB.1
    set wB := resB.2
    have hwA_lt3 : wA < n + gs3.length := by rw [hBeq, List.length_append]; omega
    set gs4 := gs3 ++ [⟨.and, [wA, wB]⟩]
    set wP := n + gs3.length
    have h4leg : legalGates n gs4 :=
      legalGates_snoc hBleg (fun i hi => by simp at hi; rcases hi with rfl | rfl; exact hwA_lt3; exact hBlt)
        ⟨by simp, Or.inl rfl⟩
    have h4cost : costGates gs4 = costGates gs3 + 1 :=
      costGates_snoc_one gs3 ⟨.and, [wA, wB]⟩ ⟨Or.inl rfl, rfl⟩
    have hacc1_lt4 : acc1 < n + gs4.length := by
      simp only [gs4, hBeq, hAeq, List.length_append, List.length_singleton]; omega
    have hwP_lt4 : wP < n + gs4.length := by simp [gs4, wP]
    have hstep := addXor_step n gs4 acc1 wP h4leg hacc1_lt4 hwP_lt4
    refine ⟨ext1 ++ extA ++ extB ++ [⟨.and, [wA, wB]⟩, ⟨.mod 2, [acc1, wP]⟩, ⟨.not, [n + gs4.length]⟩],
      ?_, ?_, ?_, ?_, ?_⟩
    · simp only [appendSumProdsLoop]
      change gs4 ++ [⟨.mod 2, [acc1, wP]⟩, ⟨.not, [n + gs4.length]⟩] = _
      simp only [gs4, hBeq, hAeq, h1eq, List.append_assoc, List.cons_append, List.nil_append]
    · exact hstep.1
    · change costGates (gs4 ++ [⟨.mod 2, [acc1, wP]⟩, ⟨.not, [n + gs4.length]⟩]) = _
      rw [hstep.2.1, h4cost, hBcost, hAcost, h1cost]; omega
    · change n + gs4.length + 1 < n + (gs4 ++ ([⟨.mod 2, [acc1, wP]⟩, ⟨.not, [n + gs4.length]⟩] : List Gate)).length
      simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · intro u
      change (wiresOf (gs4 ++ [⟨.mod 2, [acc1, wP]⟩, ⟨.not, [n + gs4.length]⟩]) (bitsOf n u)).getD (n + gs4.length + 1) false = _
      rw [hstep.2.2.2 (bitsOf n u) (bitsOf_len n u)]
      have hacc1_eq : (wiresOf gs4 (bitsOf n u)).getD acc1 false = (wiresOf gs1 (bitsOf n u)).getD acc1 false := by
        have hgs4_eq : gs4 = gs1 ++ (extA ++ extB ++ [⟨.and, [wA, wB]⟩]) := by
          simp only [gs4, hBeq, hAeq, List.append_assoc]
        rw [hgs4_eq, wiresOf_append_getD_lt gs1 _ (bitsOf n u) (by rw [bitsOf_len]; exact h1lt)]
      have hwP_eq : (wiresOf gs4 (bitsOf n u)).getD wP false =
          decide ((dotProduct (cA ⟨m, hm⟩) u + bA ⟨m, hm⟩) * (dotProduct (cB ⟨m, hm⟩) u + bB ⟨m, hm⟩) = 1) := by
        change (wiresOf (gs3 ++ [⟨.and, [wA, wB]⟩]) (bitsOf n u)).getD (n + gs3.length) false = _
        rw [wiresOf_snoc_last_eq gs3 ⟨.and, [wA, wB]⟩ (bitsOf n u) (bitsOf_len n u)]
        simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
        have hwA_val : (wiresOf gs3 (bitsOf n u)).getD wA false = decide (dotProduct (cA ⟨m, hm⟩) u + bA ⟨m, hm⟩ = 1) := by
          rw [hBeq, wiresOf_append_getD_lt gs2 extB (bitsOf n u) (by rw [bitsOf_len]; exact hAlt)]
          exact hAsem u
        rw [hwA_val, hBsem u, zmod2_mul_decide]
      rw [hacc1_eq, h1sem u, hwP_eq]
      have hsplit : (Finset.univ.filter (fun i : Fin s => i.val < m + 1)) =
          insert ⟨m, hm⟩ (Finset.univ.filter (fun i : Fin s => i.val < m)) := by
        ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
        omega
      have hnotmem : (⟨m, hm⟩ : Fin s) ∉ Finset.univ.filter (fun i : Fin s => i.val < m) := by simp
      rw [hsplit, Finset.sum_insert hnotmem, zmod2_add_decide]
      cases (wiresOf gs (bitsOf n u)).getD acc false <;>
        cases decide ((dotProduct (cA ⟨m, hm⟩) u + bA ⟨m, hm⟩) * (dotProduct (cB ⟨m, hm⟩) u + bB ⟨m, hm⟩) = 1) <;>
        cases decide ((∑ x ∈ Finset.univ.filter (fun i : Fin s => i.val < m),
          (dotProduct (cA x) u + bA x) * (dotProduct (cB x) u + bB x)) = 1) <;> decide

lemma build_sum_prods_circuit (n s : ℕ) (c0 : Fin n → F2) (b0 : F2)
    (cA cB : Fin s → Fin n → F2) (bA bB : Fin s → F2) :
    ∃ C : Circuit, legalGates n C.gates ∧ costGates C.gates = s ∧
      ∀ u : Fin n → F2, C.eval (bitsOf n u) =
        decide ((dotProduct c0 u + b0) +
          ∑ i : Fin s, (dotProduct (cA i) u + bA i) * (dotProduct (cB i) u + bB i) = 1) := by
  have hnil : legalGates n [] := ⟨fun j hj => by simp at hj, fun h hh => by simp at hh⟩
  rcases appendAffine_spec n [] c0 b0 hnil with ⟨_, _, h0leg, h0cost, h0lt, h0sem⟩
  set res0 := appendAffine n [] c0 b0
  rcases appendSumProdsLoop_spec n s cA cB bA bB s (le_refl s) res0.1 res0.2 h0leg h0lt with
    ⟨_, _, hleg, hcost, _, hsem⟩
  set res := appendSumProdsLoop n s cA cB bA bB s (le_refl s) res0.1 res0.2
  refine ⟨⟨res.1, res.2⟩, hleg, ?_, fun u => ?_⟩
  · have hc0 : costGates ([] : List Gate) = 0 := by simp [costGates]
    dsimp only [branch_r_mk, branch_U_mk, branch_gates_mk, branch_tap_mk, branch_off_mk, branch_slope_mk, res, res0] at hcost h0cost ⊢
    omega
  · change (wiresOf res.1 (bitsOf n u)).getD res.2 false = _
    rw [hsem u, h0sem u]
    have huniv : Finset.univ.filter (fun i : Fin s => i.val < s) = Finset.univ := by
      ext i; simp
    rw [huniv, ← zmod2_add_decide]

def concatVec {k : ℕ} (x y : Fin k → F2) : Fin (2 * k) → F2 :=
  fun idx => if h : idx.val < k then x ⟨idx.val, h⟩ else y ⟨idx.val - k, by omega⟩

lemma bitsOf_concatVec {k : ℕ} (x y : Fin k → F2) :
    bitsOf k x ++ bitsOf k y = bitsOf (2 * k) (concatVec x y) := by
  apply List.ext_getElem
  · simp [bitsOf_len]; omega
  · intro i h1 h2
    simp only [bitsOf]
    by_cases hik : i < k
    · rw [List.getElem_append_left (by simp; exact hik)]
      simp [concatVec, hik]
    · rw [List.getElem_append_right (by simp; omega)]
      simp [concatVec, hik]

lemma dotProduct_concatVec {k : ℕ} (u v x y : Fin k → F2) :
    dotProduct (concatVec u v) (concatVec x y) = dotProduct u x + dotProduct v y := by
  simp only [dotProduct]
  let e : Fin k ⊕ Fin k ≃ Fin (2 * k) :=
    { toFun := Sum.elim (fun i => ⟨i.val, by omega⟩) (fun i => ⟨k + i.val, by omega⟩)
      invFun := fun i => if h : i.val < k then Sum.inl ⟨i.val, h⟩ else Sum.inr ⟨i.val - k, by omega⟩
      left_inv := fun s => by
        cases s with
        | inl i => simp [i.isLt]
        | inr i =>
          have hnot : ¬ (k + i.val < k) := by omega
          simp [hnot]
      right_inv := fun i => by
        by_cases h : i.val < k
        · simp [h]
        · simp only [h, ↓reduceDIte, Sum.elim_inr]
          apply Fin.ext; dsimp; omega }
  rw [← Equiv.sum_comp e, Fintype.sum_sum_type]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp [e, concatVec, i.isLt]
  · refine Finset.sum_congr rfl fun i _ => ?_
    have hnot : ¬ (k + i.val < k) := by omega
    simp [e, concatVec, hnot]

lemma linear_map_left_inv {k s : ℕ} (B : (Fin s → F2) →ₗ[F2] (Fin k → F2))
    (hB : Function.Injective B) :
    ∃ L : (Fin k → F2) →ₗ[F2] (Fin s → F2), ∀ v : Fin s → F2, L (B v) = v := by
  obtain ⟨V', hcompl⟩ := Submodule.exists_isCompl (LinearMap.range B)
  let π : (Fin k → F2) →ₗ[F2] LinearMap.range B := Submodule.linearProjOfIsCompl (LinearMap.range B) V' hcompl
  let e : (Fin s → F2) ≃ₗ[F2] LinearMap.range B := LinearEquiv.ofInjective B hB
  refine ⟨e.symm.toLinearMap.comp π, fun v => ?_⟩
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  have hmem : B v ∈ LinearMap.range B := ⟨v, rfl⟩
  have hpi : π (B v) = ⟨B v, hmem⟩ := Submodule.linearProjOfIsCompl_apply_left hcompl ⟨B v, hmem⟩
  rw [hpi]
  have hev : e v = ⟨B v, hmem⟩ := rfl
  rw [← hev, LinearEquiv.symm_apply_apply]

lemma linear_coord_dot {k : ℕ} (ℓ : (Fin k → F2) →ₗ[F2] F2) :
    ∃ r : Fin k → F2, ∀ y : Fin k → F2, ℓ y = dotProduct r y := by
  refine ⟨fun j => ℓ (Pi.single j 1), fun y => ?_⟩
  conv_lhs => rw [vec_eq_sum_single y, map_sum]
  simp only [dotProduct, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ => by ring

lemma viaFlat_to_viaCircuit (k s : ℕ) (g : (Fin k → F2) → F2) (T : ℕ)
    (B : (Fin s → F2) →ₗ[F2] (Fin k → F2)) (a : Fin k → F2) (q : (Fin s → F2) → F2)
    (hB : Function.Injective B) (hq : isQuad q)
    (hT : T ≤ 2 ^ k * (∑ v : Fin s → F2, if g (a + B v) = q v then (1 : ℤ) else -1).natAbs) :
    ∃ C : Circuit, legalGates (2 * k) C.gates ∧ costGates C.gates ≤ s ∧
      T ≤ (∑ x : Fin k → F2, ∑ y : Fin k → F2,
        if C.eval (bitsOf k x ++ bitsOf k y) = decide (dotProduct x y + g y = 1)
        then (1 : ℤ) else -1).natAbs := by
  rcases hq with ⟨b, c, M, hq_eq⟩
  rcases linear_map_left_inv B hB with ⟨L, hLB⟩
  have hcoord : ∀ i : Fin s, ∃ r : Fin k → F2, ∀ w : Fin k → F2, L w i = dotProduct r w := fun i =>
    linear_coord_dot ((LinearMap.proj i).comp L)
  choose rv hrv using hcoord
  let c0 : Fin (2 * k) → F2 := concatVec a 0
  let b0 : F2 := b
  let cA : Fin s → Fin (2 * k) → F2 := fun i => concatVec 0 (rv i)
  let bA : Fin s → F2 := fun i => dotProduct (rv i) a
  let cB : Fin s → Fin (2 * k) → F2 := fun i =>
    concatVec (B (Pi.single i 1)) (∑ j : Fin s, M i j • rv j)
  let bB : Fin s → F2 := fun i => c i + ∑ j : Fin s, M i j * dotProduct (rv j) a
  rcases build_sum_prods_circuit (2 * k) s c0 b0 cA cB bA bB with ⟨C, hleg, hcost, heval⟩
  refine ⟨C, hleg, by omega, ?_⟩
  have hCe : ∀ x y : Fin k → F2,
      C.eval (bitsOf k x ++ bitsOf k y) =
        decide (dotProduct x (a + B (L (y + a))) + q (L (y + a)) = 1) := by
    intro x y
    rw [bitsOf_concatVec, heval (concatVec x y)]
    congr 1
    have h0 : dotProduct c0 (concatVec x y) + b0 = dotProduct x a + b := by
      simp only [c0, b0, dotProduct_concatVec, zero_dotProduct, add_zero, dotProduct_comm a x]
    have hAi : ∀ i : Fin s, dotProduct (cA i) (concatVec x y) + bA i = L (y + a) i := by
      intro i
      simp only [cA, bA, dotProduct_concatVec, zero_dotProduct, zero_add, hrv i, dotProduct_add]
    have hBi : ∀ i : Fin s, dotProduct (cB i) (concatVec x y) + bB i =
        dotProduct x (B (Pi.single i 1)) + c i + ∑ j : Fin s, M i j * L (y + a) j := by
      intro i
      simp only [cB, bB, dotProduct_concatVec, dotProduct_comm (B (Pi.single i 1)) x]
      have hsum : dotProduct (∑ j : Fin s, M i j • rv j) y + ∑ j : Fin s, M i j * dotProduct (rv j) a =
          ∑ j : Fin s, M i j * L (y + a) j := by
        rw [sum_dotProduct, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_dotProduct, smul_eq_mul, hrv j, dotProduct_add]; ring
      linear_combination hsum
    have hPB : dotProduct x (B (L (y + a))) =
        ∑ i : Fin s, L (y + a) i * dotProduct x (B (Pi.single i 1)) := by
      conv_lhs => rw [vec_eq_sum_single (L (y + a)), map_sum, dotProduct_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, dotProduct_smul, smul_eq_mul]
    rw [h0, dotProduct_add, hPB, hq_eq (L (y + a))]
    have hterms : (∑ i : Fin s, (dotProduct (cA i) (concatVec x y) + bA i) * (dotProduct (cB i) (concatVec x y) + bB i)) =
        (∑ i : Fin s, L (y + a) i * dotProduct x (B (Pi.single i 1))) +
        dotProduct c (L (y + a)) +
        ∑ i : Fin s, ∑ j : Fin s, M i j * L (y + a) i * L (y + a) j := by
      simp_rw [hAi, hBi]
      calc (∑ i : Fin s, L (y + a) i * (dotProduct x (B (Pi.single i 1)) + c i + ∑ j : Fin s, M i j * L (y + a) j))
          = ∑ i : Fin s, ((L (y + a) i * dotProduct x (B (Pi.single i 1)) + c i * L (y + a) i) +
              ∑ j : Fin s, M i j * L (y + a) i * L (y + a) j) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [mul_add, mul_add, Finset.mul_sum]
            have hinner : (∑ j : Fin s, L (y + a) i * (M i j * L (y + a) j)) =
                ∑ j : Fin s, M i j * L (y + a) i * L (y + a) j :=
              Finset.sum_congr rfl fun j _ => by ring
            rw [hinner]; ring
        _ = (∑ i : Fin s, L (y + a) i * dotProduct x (B (Pi.single i 1))) +
            dotProduct c (L (y + a)) +
            ∑ i : Fin s, ∑ j : Fin s, M i j * L (y + a) i * L (y + a) j := by
            simp only [Finset.sum_add_distrib, dotProduct]
    rw [hterms]; ring
  have htotal : (∑ x : Fin k → F2, ∑ y : Fin k → F2,
      if C.eval (bitsOf k x ++ bitsOf k y) = decide (dotProduct x y + g y = 1)
      then (1 : ℤ) else -1) =
      (2 : ℤ) ^ k * ∑ v : Fin s → F2, if g (a + B v) = q v then (1 : ℤ) else -1 := by
    rw [Finset.sum_comm]
    have hinner : ∀ y : Fin k → F2,
        (∑ x : Fin k → F2, if C.eval (bitsOf k x ++ bitsOf k y) = decide (dotProduct x y + g y = 1)
          then (1 : ℤ) else -1) =
        if y + a ∈ LinearMap.range B then
          (2 : ℤ) ^ k * (if g y = q (L (y + a)) then (1 : ℤ) else -1)
        else 0 := by
      intro y
      have hrw : ∀ x : Fin k → F2,
          (if C.eval (bitsOf k x ++ bitsOf k y) = decide (dotProduct x y + g y = 1) then (1 : ℤ) else -1) =
          signBool (decide (dotProduct (a + B (L (y + a)) + y) x = 1)) *
            (if g y = q (L (y + a)) then (1 : ℤ) else -1) := by
        intro x
        rw [hCe x y, zmod2_add_decide (dotProduct x y) (g y), agree_eq_sign, eq_f2_sign]
        have hxor : Bool.xor (decide (dotProduct x (a + B (L (y + a))) + q (L (y + a)) = 1)) (decide (dotProduct x y = 1)) =
            Bool.xor (decide (dotProduct (a + B (L (y + a)) + y) x = 1)) (decide (q (L (y + a)) = 1)) := by
          rw [← zmod2_add_decide, ← zmod2_add_decide, add_dotProduct, dotProduct_comm (a + B (L (y + a))) x,
              dotProduct_comm y x]
          congr 1; ring
        rw [hxor, signBool_xor]
        ring
      simp_rw [hrw, ← Finset.sum_mul]
      by_cases hmem : y + a ∈ LinearMap.range B
      · simp only [hmem, ↓reduceIte]
        rcases hmem with ⟨v, hv⟩
        have hzero : a + B (L (y + a)) + y = 0 := by
          rw [← hv, hLB v, hv]
          calc a + (y + a) + y = (a + a) + (y + y) := by abel
            _ = 0 := by rw [zmod2_vec_add_self, zmod2_vec_add_self, add_zero]
        simp only [hzero, zero_dotProduct]
        have hcard : (∑ _x : Fin k → F2, signBool (decide ((0 : F2) = 1))) = (2 : ℤ) ^ k := by
          change (∑ _x : Fin k → F2, (1 : ℤ)) = (2 : ℤ) ^ k
          simp [ZMod.card]
        rw [hcard]
      · simp only [hmem, ↓reduceIte]
        have hne : a + B (L (y + a)) + y ≠ 0 := by
          intro h0
          apply hmem
          refine ⟨L (y + a), ?_⟩
          have h1 : B (L (y + a)) + (a + B (L (y + a)) + y) = y + a := by
            calc B (L (y + a)) + (a + B (L (y + a)) + y)
                = (B (L (y + a)) + B (L (y + a))) + (y + a) := by abel
              _ = y + a := by rw [zmod2_vec_add_self, zero_add]
          rw [h0, add_zero] at h1
          exact h1
        rw [sum_sign_dot_univ _ hne, zero_mul]
    simp_rw [hinner]
    rw [← Finset.sum_filter]
    let f_inj : (Fin s → F2) → (Fin k → F2) := fun v => a + B v
    have hbij : Finset.univ.image f_inj = Finset.univ.filter (fun y : Fin k → F2 => y + a ∈ LinearMap.range B) := by
      ext y
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter, f_inj]
      constructor
      · rintro ⟨v, rfl⟩
        refine ⟨v, ?_⟩
        calc B v = (a + a) + B v := by rw [zmod2_vec_add_self, zero_add]
          _ = a + B v + a := by abel
      · rintro ⟨v, hv⟩
        refine ⟨v, ?_⟩
        calc a + B v = a + (y + a) := by rw [hv]
          _ = (a + a) + y := by abel
          _ = y := by rw [zmod2_vec_add_self, zero_add]
    rw [← hbij, Finset.sum_image (fun v1 _ v2 _ h => hB (add_left_cancel h)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    have harg : f_inj v + a = B v := by
      dsimp only [branch_r_mk, branch_U_mk, branch_gates_mk, branch_tap_mk, branch_off_mk, branch_slope_mk, f_inj]
      calc a + B v + a = (a + a) + B v := by abel
        _ = B v := by rw [zmod2_vec_add_self, zero_add]
    rw [harg, hLB v]
  rw [htotal, Int.natAbs_mul]
  have h2k : ((2 : ℤ) ^ k).natAbs = 2 ^ k := by
    rw [show (2 : ℤ) ^ k = ((2 ^ k : ℕ) : ℤ) by push_cast; rfl, Int.natAbs_natCast]
  rw [h2k]
  exact hT

lemma forward_decomp_bounds (k s : ℕ) (g : (Fin k → F2) → F2) (C : Circuit)
    (hleg : legalGates (2 * k) C.gates) (hcost : costGates C.gates ≤ s) :
    ∃ (N : ℕ) (r : Fin N → ℕ) (W : Fin N → Submodule F2 (Fin k → F2))
      (a : Fin N → (Fin k → F2)) (D : Fin N → Circuit) (tap : Fin N → Fin k → ℕ),
      let pos := fun (i : Fin N) (y : Fin k → F2) (j : Fin k) =>
        if ((D i).wires (bitsOf k y)).getD (tap i j) false then (1 : F2) else 0
      let Bval := fun i : Fin N =>
        (∑ y : Fin k → F2, if y - a i ∈ W i then
          signBool (Bool.xor ((D i).eval (bitsOf k y)) (decide (dotProduct (pos i y) y = 1))) *
            signBool (decide (g y = 1))
        else 0).natAbs
      0 < N ∧
      (∀ i, Module.finrank F2 (W i) = r i ∧ r i ≤ k ∧ legalGates k (D i).gates ∧
        costGates (D i).gates + r i ≤ s ∧ (D i).output < k + (D i).size ∧
        ∀ j, tap i j < k + (D i).size) ∧
      (∑ i : Fin N, 2 ^ (k - r i)) = 2 ^ k ∧
      (∀ i, Bval i ≤ 2 ^ (r i)) ∧
      (∑ x : Fin k → F2, ∑ y : Fin k → F2,
        if C.eval (bitsOf k x ++ bitsOf k y) = decide (dotProduct x y + g y = 1)
        then (1 : ℤ) else -1).natAbs ≤ ∑ i : Fin N, 2 ^ (k - r i) * Bval i := by
  have hleg' : legalGates (k + k) C.gates := by rwa [show k + k = 2 * k by omega]
  rcases decomp_835 k k C hleg' with ⟨N, r, U, a, D, tap, hNpos, hmeta, hpart, heval⟩
  let pos := fun (i : Fin N) (y : Fin k → F2) (j : Fin k) =>
    if ((D i).wires (bitsOf k y)).getD (tap i j) false then (1 : F2) else 0
  let W : Fin N → Submodule F2 (Fin k → F2) := fun i => orthoComp (U i)
  have hW_dim : ∀ i, Module.finrank F2 (W i) = r i := by
    intro i
    dsimp only [branch_r_mk, branch_U_mk, branch_gates_mk, branch_tap_mk, branch_off_mk, branch_slope_mk, W]
    have h1 := finrank_orthoComp (U i)
    have h2 := (hmeta i).1
    omega
  have hU_dim : ∀ i, Module.finrank F2 (U i) = k - r i := by
    intro i; have := (hmeta i).1; omega
  let hpart_equiv : ∀ y : Fin k → F2, (Σ i : Fin N, U i) ≃ (Fin k → F2) := fun y =>
    let idxOf : (Fin k → F2) → Fin N := fun x => (hpart y x).choose
    have hidx_mem : ∀ x, x - pos (idxOf x) y ∈ U (idxOf x) := fun x => (hpart y x).choose_spec.1
    have hidx_uniq : ∀ x i, x - pos i y ∈ U i → i = idxOf x := fun x i hi => (hpart y x).choose_spec.2 i hi
    { toFun := fun p => pos p.1 y + p.2.val
      invFun := fun x => ⟨idxOf x, ⟨x - pos (idxOf x) y, hidx_mem x⟩⟩
      left_inv := fun ⟨i, ⟨u, hu⟩⟩ => by
        have hmem : pos i y + u - pos i y ∈ U i := by simpa using hu
        have hi : idxOf (pos i y + u) = i := (hidx_uniq (pos i y + u) i hmem).symm
        dsimp only
        generalize hidx_mem (pos i y + u) = hjm
        revert hjm
        generalize idxOf (pos i y + u) = j at hi ⊢
        subst hi
        intro _
        congr 1
        apply Subtype.ext
        simp
      right_inv := fun x => by
        show pos (idxOf x) y + (x - pos (idxOf x) y) = x
        abel }
  have hsum_pow : (∑ i : Fin N, 2 ^ (k - r i)) = 2 ^ k := by
    have hcard_sig : Fintype.card (Σ i : Fin N, U i) = ∑ i : Fin N, 2 ^ (k - r i) := by
      rw [Fintype.card_sigma]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [card_submodule_zmod2, hU_dim i]
    have hcard_V : Fintype.card (Fin k → F2) = 2 ^ k := by simp [ZMod.card]
    rw [← hcard_sig, ← hcard_V]
    exact Fintype.card_congr (hpart_equiv 0)
  have hprof : ∀ y : Fin k → F2,
      (∑ x : Fin k → F2, signBool (Bool.xor (C.eval (bitsOf k x ++ bitsOf k y)) (decide (dotProduct x y = 1)))) =
      ∑ i : Fin N, (2 : ℤ) ^ (k - r i) *
        (if y - a i ∈ W i then
          signBool (Bool.xor ((D i).eval (bitsOf k y)) (decide (dotProduct (pos i y) y = 1)))
        else 0) := by
    intro y
    rw [← Equiv.sum_comp (hpart_equiv y), Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hterm : ∀ u : U i,
        signBool (Bool.xor (C.eval (bitsOf k (pos i y + u.val) ++ bitsOf k y))
          (decide (dotProduct (pos i y + u.val) y = 1))) =
        signBool (Bool.xor ((D i).eval (bitsOf k y)) (decide (dotProduct (pos i y) y = 1))) *
          signBool (decide (dotProduct (y - a i) u.val = 1)) := by
      intro u
      rw [heval i y u.val u.property, add_dotProduct, zmod2_add_decide, signBool_xor, signBool_xor, signBool_xor]
      have hdot_eq : dotProduct (y - a i) u.val = dotProduct (a i) u.val + dotProduct u.val y := by
        rw [zmod2_vec_sub_eq_add, add_dotProduct, dotProduct_comm u.val y]; ring
      rw [hdot_eq, zmod2_add_decide, signBool_xor, signBool_xor]
      ring
    have heq_fn : ∀ u : U i, hpart_equiv y ⟨i, u⟩ = pos i y + u.val := fun _ => by dsimp [branch_r_mk, branch_U_mk, branch_gates_mk, branch_tap_mk, branch_off_mk, branch_slope_mk, hpart_equiv]
    simp_rw [heq_fn, hterm, ← Finset.mul_sum, sum_sign_dot_submodule (U i) (y - a i), hU_dim i]
    dsimp only [branch_r_mk, branch_U_mk, branch_gates_mk, branch_tap_mk, branch_off_mk, branch_slope_mk, W]
    split_ifs <;> ring
  refine ⟨N, r, W, a, D, tap, hNpos, ?_, hsum_pow, ?_, ?_⟩
  · intro i
    have hm := hmeta i
    exact ⟨hW_dim i, by omega, hm.2.1, by omega, hm.2.2.2.1, hm.2.2.2.2⟩
  · intro i
    dsimp only
    have hle : (∑ y : Fin k → F2, if y - a i ∈ W i then
        signBool (Bool.xor ((D i).eval (bitsOf k y)) (decide (dotProduct (pos i y) y = 1))) *
          signBool (decide (g y = 1))
      else 0).natAbs ≤
        ∑ y : Fin k → F2, (if y - a i ∈ W i then (1 : ℕ) else 0) := by
      have htri := Finset.abs_sum_le_sum_abs
        (fun y : Fin k → F2 => if y - a i ∈ W i then
          signBool (Bool.xor ((D i).eval (bitsOf k y)) (decide (dotProduct (pos i y) y = 1))) *
            signBool (decide (g y = 1))
        else 0) Finset.univ
      have habs : ∀ y : Fin k → F2,
          |(if y - a i ∈ W i then
            signBool (Bool.xor ((D i).eval (bitsOf k y)) (decide (dotProduct (pos i y) y = 1))) *
              signBool (decide (g y = 1))
          else 0)| = if y - a i ∈ W i then (1 : ℤ) else 0 := by
        intro y
        split_ifs
        · rw [abs_mul, signBool_abs_one, signBool_abs_one, mul_one]
        · simp
      simp_rw [habs] at htri
      have hnat : ((∑ y : Fin k → F2, if y - a i ∈ W i then
          signBool (Bool.xor ((D i).eval (bitsOf k y)) (decide (dotProduct (pos i y) y = 1))) *
            signBool (decide (g y = 1))
        else 0).natAbs : ℤ) ≤ ∑ y : Fin k → F2, if y - a i ∈ W i then (1 : ℤ) else 0 := by
        simpa [Int.natCast_natAbs] using htri
      exact_mod_cast hnat
    have hcard_coset : (∑ y : Fin k → F2, if y - a i ∈ W i then (1 : ℕ) else 0) = 2 ^ (r i) := by
      rw [← Finset.card_filter]
      let eW : W i ≃ {y : Fin k → F2 // y - a i ∈ W i} :=
        { toFun := fun w => ⟨a i + w.val, by simpa using w.property⟩
          invFun := fun y => ⟨y.val - a i, y.property⟩
          left_inv := fun w => Subtype.ext (by show a i + w.val - a i = w.val; abel)
          right_inv := fun y => Subtype.ext (by show a i + (y.val - a i) = y.val; abel) }
      have hc : (Finset.univ.filter (fun y : Fin k → F2 => y - a i ∈ W i)).card =
          Fintype.card {y : Fin k → F2 // y - a i ∈ W i} := (Fintype.card_subtype _).symm
      rw [hc, ← Fintype.card_congr eW, card_submodule_zmod2, hW_dim i]
    exact le_trans hle (le_of_eq hcard_coset)
  · dsimp only
    have hsum_eq : (∑ x : Fin k → F2, ∑ y : Fin k → F2,
        if C.eval (bitsOf k x ++ bitsOf k y) = decide (dotProduct x y + g y = 1)
        then (1 : ℤ) else -1) =
        ∑ i : Fin N, (2 : ℤ) ^ (k - r i) *
          (∑ y : Fin k → F2, if y - a i ∈ W i then
            signBool (Bool.xor ((D i).eval (bitsOf k y)) (decide (dotProduct (pos i y) y = 1))) *
              signBool (decide (g y = 1))
          else 0) := by
      rw [Finset.sum_comm]
      have hy : ∀ y : Fin k → F2,
          (∑ x : Fin k → F2, if C.eval (bitsOf k x ++ bitsOf k y) = decide (dotProduct x y + g y = 1)
            then (1 : ℤ) else -1) =
          (∑ i : Fin N, (2 : ℤ) ^ (k - r i) *
            (if y - a i ∈ W i then
              signBool (Bool.xor ((D i).eval (bitsOf k y)) (decide (dotProduct (pos i y) y = 1))) *
                signBool (decide (g y = 1))
            else 0)) := by
        intro y
        have hstep : ∀ x : Fin k → F2,
            (if C.eval (bitsOf k x ++ bitsOf k y) = decide (dotProduct x y + g y = 1) then (1 : ℤ) else -1) =
            signBool (Bool.xor (C.eval (bitsOf k x ++ bitsOf k y)) (decide (dotProduct x y = 1))) *
              signBool (decide (g y = 1)) := by
          intro x
          rw [zmod2_add_decide, agree_eq_sign]
        simp_rw [hstep, ← Finset.sum_mul, hprof y, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        split_ifs <;> ring
      simp_rw [hy]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
    rw [hsum_eq]
    have htri := Finset.abs_sum_le_sum_abs
      (fun i : Fin N => (2 : ℤ) ^ (k - r i) *
        (∑ y : Fin k → F2, if y - a i ∈ W i then
          signBool (Bool.xor ((D i).eval (bitsOf k y)) (decide (dotProduct (pos i y) y = 1))) *
            signBool (decide (g y = 1))
        else 0)) Finset.univ
    have habs_term : ∀ i : Fin N,
        |(2 : ℤ) ^ (k - r i) *
          (∑ y : Fin k → F2, if y - a i ∈ W i then
            signBool (Bool.xor ((D i).eval (bitsOf k y)) (decide (dotProduct (pos i y) y = 1))) *
              signBool (decide (g y = 1))
          else 0)| =
        ((2 ^ (k - r i) * (∑ y : Fin k → F2, if y - a i ∈ W i then
          signBool (Bool.xor ((D i).eval (bitsOf k y)) (decide (dotProduct (pos i y) y = 1))) *
            signBool (decide (g y = 1))
        else 0).natAbs : ℕ) : ℤ) := by
      intro i
      rw [abs_mul, abs_of_nonneg (by positivity), ← Int.natCast_natAbs]
      push_cast; rfl
    simp_rw [habs_term] at htri
    have hnat : ((∑ i : Fin N, (2 : ℤ) ^ (k - r i) *
        (∑ y : Fin k → F2, if y - a i ∈ W i then
          signBool (Bool.xor ((D i).eval (bitsOf k y)) (decide (dotProduct (pos i y) y = 1))) *
            signBool (decide (g y = 1))
        else 0)).natAbs : ℤ) ≤
        ((∑ i : Fin N, 2 ^ (k - r i) * (∑ y : Fin k → F2, if y - a i ∈ W i then
          signBool (Bool.xor ((D i).eval (bitsOf k y)) (decide (dotProduct (pos i y) y = 1))) *
            signBool (decide (g y = 1))
        else 0).natAbs : ℕ) : ℤ) := by
      simpa [Int.natCast_natAbs, Nat.cast_sum] using htri
    exact Int.ofNat_le.mp hnat

lemma viaCircuit_le_bound (k s : ℕ) (g : (Fin k → F2) → F2) (T : ℕ)
    (C : Circuit) (hleg : legalGates (2 * k) C.gates) (hcost : costGates C.gates ≤ s)
    (hT : T ≤ (∑ x : Fin k → F2, ∑ y : Fin k → F2,
      if C.eval (bitsOf k x ++ bitsOf k y) = decide (dotProduct x y + g y = 1)
      then (1 : ℤ) else -1).natAbs) :
    T ≤ 2 ^ (k + s) := by
  rcases forward_decomp_bounds k s g C hleg hcost with ⟨N, r, W, a, D, tap, _, hmeta, hsum, hB, hraw⟩
  dsimp only at hB hraw
  have hbound : ∑ i : Fin N, 2 ^ (k - r i) *
      (∑ y : Fin k → F2, if y - a i ∈ W i then
        signBool (Bool.xor ((D i).eval (bitsOf k y))
          (decide (dotProduct (fun j : Fin k => if ((D i).wires (bitsOf k y)).getD (tap i j) false then (1 : F2) else 0) y = 1))) *
          signBool (decide (g y = 1))
      else 0).natAbs ≤ ∑ i : Fin N, 2 ^ (k - r i) * 2 ^ s := by
    refine Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ ?_
    have hri : r i ≤ s := by have := (hmeta i).2.2.2.1; omega
    exact le_trans (hB i) (Nat.pow_le_pow_right (by omega) hri)
  have hrhs : ∑ i : Fin N, 2 ^ (k - r i) * 2 ^ s = 2 ^ (k + s) := by
    rw [← Finset.sum_mul, hsum, ← pow_add]
  exact le_trans hT (le_trans hraw (le_trans hbound (le_of_eq hrhs)))

lemma viaCircuit_to_viaFlat (k s : ℕ) (g : (Fin k → F2) → F2) (T : ℕ)
    (hbig : 2 ^ (k + s) < 2 * T)
    (C : Circuit) (hleg : legalGates (2 * k) C.gates) (hcost : costGates C.gates ≤ s)
    (hT : T ≤ (∑ x : Fin k → F2, ∑ y : Fin k → F2,
      if C.eval (bitsOf k x ++ bitsOf k y) = decide (dotProduct x y + g y = 1)
      then (1 : ℤ) else -1).natAbs) :
    ∃ (B : (Fin s → F2) →ₗ[F2] (Fin k → F2)) (a : Fin k → F2) (q : (Fin s → F2) → F2),
      Function.Injective B ∧ isQuad q ∧
      T ≤ 2 ^ k * (∑ v : Fin s → F2, if g (a + B v) = q v then (1 : ℤ) else -1).natAbs := by
  rcases forward_decomp_bounds k s g C hleg hcost with ⟨N, r, W, a, D, tap, hNpos, hmeta, hsum, hB, hraw⟩
  set pos := fun (i : Fin N) (y : Fin k → F2) (j : Fin k) =>
    if ((D i).wires (bitsOf k y)).getD (tap i j) false then (1 : F2) else 0
  set Bval := fun i : Fin N =>
    (∑ y : Fin k → F2, if y - a i ∈ W i then
      signBool (Bool.xor ((D i).eval (bitsOf k y)) (decide (dotProduct (pos i y) y = 1))) *
        signBool (decide (g y = 1))
    else 0).natAbs
  have hex : ∃ i0 : Fin N, T ≤ 2 ^ k * Bval i0 := by
    by_contra hnot
    push Not at hnot
    have hlt_sum : ∑ i : Fin N, 2 ^ (k - r i) * (2 ^ k * Bval i) < ∑ i : Fin N, 2 ^ (k - r i) * T := by
      apply Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.mpr ⟨⟨0, hNpos⟩⟩)
      intro i _
      exact Nat.mul_lt_mul_of_pos_left (hnot i) (Nat.pow_pos (by omega))
    have hlhs : ∑ i : Fin N, 2 ^ (k - r i) * (2 ^ k * Bval i) = 2 ^ k * ∑ i : Fin N, 2 ^ (k - r i) * Bval i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by ring
    have hrhs : ∑ i : Fin N, 2 ^ (k - r i) * T = 2 ^ k * T := by
      rw [← Finset.sum_mul, hsum]
    rw [hlhs, hrhs] at hlt_sum
    have hle : 2 ^ k * T ≤ 2 ^ k * ∑ i : Fin N, 2 ^ (k - r i) * Bval i :=
      Nat.mul_le_mul_left _ (le_trans hT hraw)
    omega
  rcases hex with ⟨i0, hi0⟩
  have hm := hmeta i0
  have hBi0 : Bval i0 ≤ 2 ^ (r i0) := hB i0
  have hpow_lt : 2 ^ (k + s) < 2 ^ (k + r i0 + 1) := by
    have h1 : 2 * T ≤ 2 * (2 ^ k * Bval i0) := Nat.mul_le_mul_left 2 hi0
    have h2 : 2 * (2 ^ k * Bval i0) ≤ 2 * (2 ^ k * 2 ^ (r i0)) :=
      Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left (2 ^ k) hBi0)
    have h3 : 2 * (2 ^ k * 2 ^ (r i0)) = 2 ^ (k + r i0 + 1) := by
      rw [pow_succ, pow_add]; ring
    omega
  have hs_le_r : s ≤ r i0 := by
    by_contra hlt
    push Not at hlt
    have hle : 2 ^ (k + r i0 + 1) ≤ 2 ^ (k + s) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hr_eq : r i0 = s := by omega
  have hcost0 : costGates (D i0).gates = 0 := by omega
  have haff := cost_zero_affine (D i0).gates hm.2.2.1 hcost0
  obtain ⟨d_out, c_out, hd_out⟩ := haff (D i0).output hm.2.2.2.2.1
  have htap_aff : ∀ j : Fin k, ∃ (lin : Fin k → F2) (c : F2), ∀ y : Fin k → F2,
      pos i0 y j = dotProduct lin y + c := by
    intro j
    obtain ⟨lin, c, hlin⟩ := haff (tap i0 j) (hm.2.2.2.2.2 j)
    refine ⟨lin, c, fun y => ?_⟩
    dsimp only [branch_r_mk, branch_U_mk, branch_gates_mk, branch_tap_mk, branch_off_mk, branch_slope_mk, pos]
    change (if (wiresOf (D i0).gates (bitsOf k y)).getD (tap i0 j) false then (1 : F2) else 0) = _
    rw [hlin y, zmod2_decide_bool]
  choose L_tap c_tap hL_tap using htap_aff
  have hdimW : Module.finrank F2 (W i0) = s := by rw [hm.1, hr_eq]
  let e : (Fin s → F2) ≃ₗ[F2] W i0 :=
    LinearEquiv.ofFinrankEq (Fin s → F2) (W i0) (by rw [Module.finrank_fin_fun, hdimW])
  let B : (Fin s → F2) →ₗ[F2] (Fin k → F2) := (W i0).subtype.comp e.toLinearMap
  have hB_inj : Function.Injective B := Subtype.val_injective.comp e.injective
  let Q : (Fin k → F2) → F2 := fun y =>
    (dotProduct d_out y + c_out) + ∑ j : Fin k, (dotProduct (L_tap j) y + c_tap j) * y j
  let q : (Fin s → F2) → F2 := fun v => Q (a i0 + B v)
  have hq_quad : isQuad q := by
    obtain ⟨u0, b0, hu0⟩ := linear_comp_affine B (a i0) d_out c_out
    have hq0 : isQuad (fun v => dotProduct d_out (a i0 + B v) + c_out) := by
      have : (fun v => dotProduct d_out (a i0 + B v) + c_out) = (fun v => dotProduct u0 v + b0) :=
        funext hu0
      rw [this]; exact isQuad_affine u0 b0
    have hq_sum : isQuad (fun v => ∑ j : Fin k, (dotProduct (L_tap j) (a i0 + B v) + c_tap j) * (a i0 + B v) j) := by
      apply isQuad_finset_sum Finset.univ
      intro j _
      obtain ⟨u1, b1, hu1⟩ := linear_comp_affine B (a i0) (L_tap j) (c_tap j)
      obtain ⟨u2, b2, hu2⟩ := linear_comp_affine B (a i0) (Pi.single j 1) 0
      have hprod : (fun v => (dotProduct (L_tap j) (a i0 + B v) + c_tap j) * (a i0 + B v) j) =
          (fun v => (dotProduct u1 v + b1) * (dotProduct u2 v + b2)) := by
        funext v
        have hcoord : (a i0 + B v) j = dotProduct u2 v + b2 := by
          have := hu2 v
          simpa [single_dotProduct] using this
        rw [hu1 v, hcoord]
      rw [hprod]
      exact isQuad_mul_affine u1 u2 b1 b2
    exact isQuad_add hq0 hq_sum
  have hBval_eq : Bval i0 = (∑ v : Fin s → F2, if g (a i0 + B v) = q v then (1 : ℤ) else -1).natAbs := by
    dsimp only [branch_r_mk, branch_U_mk, branch_gates_mk, branch_tap_mk, branch_off_mk, branch_slope_mk, Bval]
    congr 1
    rw [← Finset.sum_filter]
    let f_inj : (Fin s → F2) → (Fin k → F2) := fun v => a i0 + B v
    have hbij : Finset.univ.image f_inj = Finset.univ.filter (fun y : Fin k → F2 => y - a i0 ∈ W i0) := by
      ext y
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter, f_inj]
      constructor
      · rintro ⟨v, rfl⟩
        have : a i0 + B v - a i0 = (e v).val := by
          show a i0 + (e v).val - a i0 = (e v).val; abel
        rw [this]; exact (e v).property
      · intro hy
        refine ⟨e.symm ⟨y - a i0, hy⟩, ?_⟩
        show a i0 + (e (e.symm ⟨y - a i0, hy⟩)).val = y
        rw [LinearEquiv.apply_symm_apply]
        exact add_sub_cancel (a i0) y
    rw [← hbij, Finset.sum_image (fun v1 _ v2 _ h => hB_inj (add_left_cancel h))]
    refine Finset.sum_congr rfl fun v _ => ?_
    have hDeval : (D i0).eval (bitsOf k (f_inj v)) = decide (dotProduct d_out (f_inj v) + c_out = 1) :=
      hd_out (f_inj v)
    have hdotp : dotProduct (pos i0 (f_inj v)) (f_inj v) =
        ∑ j : Fin k, (dotProduct (L_tap j) (f_inj v) + c_tap j) * (f_inj v) j := by
      simp only [dotProduct, hL_tap]
    rw [hDeval, hdotp, ← zmod2_add_decide]
    change signBool (decide (q v = 1)) * signBool (decide (g (a i0 + B v) = 1)) = _
    rw [eq_f2_sign, mul_comm]
  refine ⟨B, a i0, q, hB_inj, hq_quad, ?_⟩
  rwa [← hBval_eq]

end PEqualNP.Outside.L_meta_32057_aux


namespace PEqualNP.Outside.L_meta_32057_aux.LineCircuit

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

abbrev F2 := ZMod 2

def legalGates (n : ℕ) (gs : List Gate) : Prop :=
  ReadsBack n ⟨gs, 0⟩ ∧
    ∀ h ∈ gs, h.inputs.length ≤ 2 ∧
      (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1))

noncomputable def costGates (gs : List Gate) : ℕ :=
  gs.countP (fun h => @decide ((h.op = .and ∨ h.op = .or) ∧ h.inputs.length = 2) (Classical.propDecidable _))

def wiresOf (gs : List Gate) (x : List Bool) : List Bool :=
  (Circuit.mk gs 0).wires x

def bitsOf (n : ℕ) (u : Fin n → F2) : List Bool :=
  List.ofFn (fun j : Fin n => decide (u j = 1))

lemma bitsOf_len (n : ℕ) (u : Fin n → F2) : (bitsOf n u).length = n := by
  simp [bitsOf]

lemma bitsOf_getD (n : ℕ) (u : Fin n → F2) (j : Fin n) :
    (bitsOf n u).getD j.val false = decide (u j = 1) := by
  simp [bitsOf, List.getD_eq_getElem?_getD, j.isLt]

lemma zmod2_add_decide (a b : F2) :
    decide (a + b = 1) = Bool.xor (decide (a = 1)) (decide (b = 1)) := by
  fin_cases a <;> fin_cases b <;> decide

lemma zmod2_mul_decide (a b : F2) :
    decide (a * b = 1) = (decide (a = 1) && decide (b = 1)) := by
  fin_cases a <;> fin_cases b <;> decide

lemma zmod2_bool_decide (b : Bool) :
    decide ((if b then (1 : F2) else 0) = 1) = b := by
  cases b <;> decide

lemma zmod2_cases (a : F2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma zmod2_xor_zero_iff (b ow : Bool) (d : F2) :
    d + (if Bool.xor b ow then (1 : F2) else 0) = 0 ↔ b = Bool.xor ow (decide (d = 1)) := by
  cases b <;> cases ow <;> fin_cases d <;> decide

lemma zmod2_decide_bool (a : F2) :
    (if decide (a = 1) then (1 : F2) else 0) = a := by
  fin_cases a <;> rfl

lemma zmod2_sub_eq_add (a b : F2) : a - b = a + b := by
  fin_cases a <;> fin_cases b <;> decide

lemma zmod2_vec_sub_eq_add {k : ℕ} (x y : Fin k → F2) : x - y = x + y := by
  funext j; exact zmod2_sub_eq_add (x j) (y j)

lemma zmod2_vec_add_self {k : ℕ} (x : Fin k → F2) : x + x = 0 := by
  funext j
  have : x j + x j = 0 := by
    rcases zmod2_cases (x j) with h | h <;> rw [h] <;> decide
  exact this

lemma wiresOf_len (gs : List Gate) (x : List Bool) :
    (wiresOf gs x).length = x.length + gs.length := by
  unfold wiresOf Circuit.wires
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
    omega

lemma wiresOf_append (gs1 gs2 : List Gate) (x : List Bool) :
    wiresOf (gs1 ++ gs2) x = wiresOf gs2 (wiresOf gs1 x) := by
  unfold wiresOf Circuit.wires
  exact List.foldl_append

lemma wiresOf_getD_lt (gs : List Gate) (x : List Bool) {i : ℕ} (hi : i < x.length) :
    (wiresOf gs x).getD i false = x.getD i false := by
  unfold wiresOf Circuit.wires
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hi' : i < (x ++ [g.op.eval (g.inputs.map fun idx => x.getD idx false)]).length := by
      simp only [List.length_append, List.length_cons, List.length_nil]; omega
    rw [ih _ hi']
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma wiresOf_append_getD_lt (gs1 gs2 : List Gate) (x : List Bool) {i : ℕ}
    (hi : i < x.length + gs1.length) :
    (wiresOf (gs1 ++ gs2) x).getD i false = (wiresOf gs1 x).getD i false := by
  rw [wiresOf_append, wiresOf_getD_lt gs2 (wiresOf gs1 x) (by rw [wiresOf_len]; exact hi)]

lemma wiresOf_snoc_last (gs : List Gate) (g : Gate) (x : List Bool) :
    (wiresOf (gs ++ [g]) x).getD (x.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (wiresOf gs x).getD i false) := by
  rw [wiresOf_append]
  set w := wiresOf gs x
  have hlen : w.length = x.length + gs.length := wiresOf_len gs x
  change (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).getD (x.length + gs.length) false = _
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
      show x.length + gs.length - w.length = 0 by omega]
  rfl

lemma wiresOf_snoc_last_eq {n : ℕ} (gs : List Gate) (g : Gate) (x : List Bool) (hx : x.length = n) :
    (wiresOf (gs ++ [g]) x).getD (n + gs.length) false =
      g.op.eval (g.inputs.map fun i => (wiresOf gs x).getD i false) := by
  have h := wiresOf_snoc_last gs g x
  rw [hx] at h
  exact h

lemma readsBack_append {n : ℕ} {gs1 gs2 : List Gate}
    (h1 : ReadsBack n ⟨gs1, 0⟩)
    (h2 : ∀ j < gs2.length, ∀ i ∈ (gs2.getD j ⟨.or, []⟩).inputs, i < n + gs1.length + j) :
    ReadsBack n ⟨gs1 ++ gs2, 0⟩ := by
  intro j hj i hi
  simp only [gateAt] at hi
  simp only [List.length_append] at hj
  by_cases hlt : j < gs1.length
  · have hget : (gs1 ++ gs2).getD j ⟨.or, []⟩ = gs1.getD j ⟨.or, []⟩ := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
    rw [hget] at hi
    exact h1 j hlt i hi
  · have hge : gs1.length ≤ j := by omega
    have hget : (gs1 ++ gs2).getD j ⟨.or, []⟩ = gs2.getD (j - gs1.length) ⟨.or, []⟩ := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hge]
    rw [hget] at hi
    have := h2 (j - gs1.length) (by omega) i hi
    omega

lemma legalGates_snoc {n : ℕ} {gs : List Gate} {g : Gate}
    (hgs : legalGates n gs)
    (hback : ∀ i ∈ g.inputs, i < n + gs.length)
    (hshape : g.inputs.length ≤ 2 ∧
      (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))) :
    legalGates n (gs ++ [g]) := by
  refine ⟨readsBack_append hgs.1 ?_, ?_⟩
  · intro j hj i hi
    have hj0 : j = 0 := by simp at hj; omega
    subst hj0
    simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero, Option.getD_some] at hi
    have := hback i hi
    omega
  · intro h hh
    rcases List.mem_append.mp hh with h1 | h2
    · exact hgs.2 h h1
    · simp only [List.mem_singleton] at h2; subst h2; exact hshape

lemma legalGates_prefix {n : ℕ} {gs : List Gate} {g : Gate}
    (h : legalGates n (gs ++ [g])) :
    legalGates n gs ∧
      (∀ i ∈ g.inputs, i < n + gs.length) ∧
      (g.inputs.length ≤ 2 ∧
        (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))) := by
  refine ⟨⟨?_, fun h' hh' => h.2 h' (List.mem_append_left _ hh')⟩, ?_, h.2 g (by simp)⟩
  · intro j hj i hi
    have hj0 : j < gs.length := hj
    have hj' : j < (gs ++ [g]).length := by simp; omega
    have hget : (gs ++ [g]).getD j ⟨.or, []⟩ = gs.getD j ⟨.or, []⟩ := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hj0]
    have hi' : i ∈ (gateAt ⟨gs ++ [g], 0⟩ j).inputs := by
      change i ∈ ((gs ++ [g]).getD j ⟨.or, []⟩).inputs
      rw [hget]; exact hi
    exact h.1 j hj' i hi'
  · intro i hi
    have hj' : gs.length < (gs ++ [g]).length := by simp
    have hget : (gs ++ [g]).getD gs.length ⟨.or, []⟩ = g := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self,
        List.getElem?_cons_zero, Option.getD_some]
    exact h.1 gs.length hj' i (by simpa [gateAt, hget] using hi)

lemma costGates_append (gs1 gs2 : List Gate) :
    costGates (gs1 ++ gs2) = costGates gs1 + costGates gs2 := by
  unfold costGates; exact List.countP_append

lemma costGates_snoc_zero (gs : List Gate) (g : Gate)
    (h0 : ¬ ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2)) :
    costGates (gs ++ [g]) = costGates gs := by
  rw [costGates_append]
  unfold costGates
  simp [h0]

lemma costGates_snoc_one (gs : List Gate) (g : Gate)
    (h1 : (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) :
    costGates (gs ++ [g]) = costGates gs + 1 := by
  rw [costGates_append]
  unfold costGates
  simp [h1]

lemma addXor_step (t : ℕ) (gs : List Gate) (w1 w2 : ℕ)
    (hgs : legalGates t gs) (hw1 : w1 < t + gs.length) (hw2 : w2 < t + gs.length) :
    let gs' := gs ++ [⟨.mod 2, [w1, w2]⟩, ⟨.not, [t + gs.length]⟩]
    legalGates t gs' ∧
    costGates gs' = costGates gs ∧
    gs'.length = gs.length + 2 ∧
    ∀ x : List Bool, x.length = t →
      (wiresOf gs' x).getD (t + gs.length + 1) false =
        Bool.xor ((wiresOf gs x).getD w1 false) ((wiresOf gs x).getD w2 false) := by
  intro gs'
  have h1 : legalGates t (gs ++ [⟨.mod 2, [w1, w2]⟩]) := by
    apply legalGates_snoc hgs
    · intro i hi; simp at hi; rcases hi with rfl | rfl <;> omega
    · exact ⟨by simp, Or.inr (Or.inr (Or.inl rfl))⟩
  have h2 : legalGates t ((gs ++ [⟨.mod 2, [w1, w2]⟩]) ++ [⟨.not, [t + gs.length]⟩]) := by
    apply legalGates_snoc h1
    · intro i hi; simp at hi; subst hi; simp
    · exact ⟨by simp, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
  have hgs'_eq : gs' = (gs ++ [⟨.mod 2, [w1, w2]⟩]) ++ [⟨.not, [t + gs.length]⟩] := by simp [gs']
  refine ⟨hgs'_eq ▸ h2, ?_, by simp [gs'], ?_⟩
  · rw [hgs'_eq,
        costGates_snoc_zero (gs ++ [(⟨.mod 2, [w1, w2]⟩ : Gate)]) (⟨.not, [t + gs.length]⟩ : Gate) (by simp),
        costGates_snoc_zero gs (⟨.mod 2, [w1, w2]⟩ : Gate) (by simp)]
  · intro x hx
    rw [hgs'_eq]
    have hidx : t + gs.length + 1 = x.length + (gs ++ [(⟨.mod 2, [w1, w2]⟩ : Gate)]).length := by simp; omega
    rw [hidx, wiresOf_snoc_last]
    have hidx1 : t + gs.length = x.length + gs.length := by omega
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.headD_cons]
    rw [hidx1, wiresOf_snoc_last]
    simp only [List.map_cons, List.map_nil, GateOp.eval]
    cases (wiresOf gs x).getD w1 false <;> cases (wiresOf gs x).getD w2 false <;> decide

lemma appendConst_spec (n : ℕ) (gs : List Gate) (b : F2) (hgs : legalGates n gs) :
    let g := if b = 1 then Gate.mk .and [] else Gate.mk .or []
    let gs' := gs ++ [g]
    legalGates n gs' ∧
    costGates gs' = costGates gs ∧
    n + gs.length < n + gs'.length ∧
    ∀ x : List Bool, x.length = n →
      (wiresOf gs' x).getD (n + gs.length) false = decide (b = 1) := by
  intro g gs'
  have hshape : g.inputs.length ≤ 2 ∧
      (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1)) := by
    dsimp only [g]; split_ifs
    · exact ⟨by simp, Or.inl rfl⟩
    · exact ⟨by simp, Or.inr (Or.inl rfl)⟩
  have hback : ∀ i ∈ g.inputs, i < n + gs.length := by
    dsimp only [g]; split_ifs <;> simp
  refine ⟨legalGates_snoc hgs hback hshape, ?_, by simp [gs'], ?_⟩
  · apply costGates_snoc_zero gs g
    dsimp only [g]; split_ifs <;> simp
  · intro x hx
    rw [wiresOf_snoc_last_eq gs g x hx]
    rcases zmod2_cases b with rfl | rfl <;> simp [g, GateOp.eval]

def appendAffineLoop (n : ℕ) (c : Fin n → F2) : (m : ℕ) → m ≤ n → List Gate → ℕ → List Gate × ℕ
  | 0, _, gs, acc => (gs, acc)
  | m + 1, hm, gs, acc =>
    let res := appendAffineLoop n c m (by omega) gs acc
    let gs1 := res.1
    let acc1 := res.2
    if c ⟨m, hm⟩ = 1 then
      (gs1 ++ [⟨.mod 2, [acc1, m]⟩, ⟨.not, [n + gs1.length]⟩], n + gs1.length + 1)
    else (gs1, acc1)

lemma appendAffineLoop_spec (n : ℕ) (c : Fin n → F2) :
    ∀ (m : ℕ) (hm : m ≤ n) (gs : List Gate) (acc : ℕ),
      legalGates n gs → acc < n + gs.length →
      let res := appendAffineLoop n c m hm gs acc
      ∃ ext : List Gate,
        res.1 = gs ++ ext ∧
        legalGates n res.1 ∧
        costGates res.1 = costGates gs ∧
        res.2 < n + res.1.length ∧
        ∀ u : Fin n → F2,
          (wiresOf res.1 (bitsOf n u)).getD res.2 false =
            Bool.xor ((wiresOf gs (bitsOf n u)).getD acc false)
              (decide ((∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < m), c j * u j) = 1)) := by
  intro m
  induction m with
  | zero =>
    intro hm gs acc hleg hacc
    refine ⟨[], by simp [appendAffineLoop], hleg, rfl, hacc, fun u => ?_⟩
    have hemp : Finset.univ.filter (fun j : Fin n => j.val < 0) = ∅ := by ext j; simp
    simp [appendAffineLoop, hemp]
  | succ m ih =>
    intro hm gs acc hleg hacc
    rcases ih (by omega) gs acc hleg hacc with ⟨ext1, h1eq, h1leg, h1cost, h1lt, h1sem⟩
    set gs1 := (appendAffineLoop n c m (by omega) gs acc).1
    set acc1 := (appendAffineLoop n c m (by omega) gs acc).2
    have hsplit : (Finset.univ.filter (fun j : Fin n => j.val < m + 1)) =
        insert ⟨m, hm⟩ (Finset.univ.filter (fun j : Fin n => j.val < m)) := by
      ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
      omega
    have hnotmem : (⟨m, hm⟩ : Fin n) ∉ Finset.univ.filter (fun j : Fin n => j.val < m) := by simp
    by_cases hcm : c ⟨m, hm⟩ = 1
    · have hstep := addXor_step n gs1 acc1 m h1leg h1lt (by omega)
      refine ⟨ext1 ++ [⟨.mod 2, [acc1, m]⟩, ⟨.not, [n + gs1.length]⟩], ?_, ?_, ?_, ?_, ?_⟩
      · simp [appendAffineLoop, hcm, gs1, acc1, h1eq, List.append_assoc]
      · simpa [appendAffineLoop, hcm, gs1, acc1] using hstep.1
      · simpa [appendAffineLoop, hcm, gs1, acc1, h1cost] using hstep.2.1
      · simp only [appendAffineLoop, hcm, ↓reduceIte, List.length_append, List.length_cons, List.length_nil]
        omega
      · intro u
        simp only [appendAffineLoop, hcm, ↓reduceIte]
        change (wiresOf (gs1 ++ [⟨.mod 2, [acc1, m]⟩, ⟨.not, [n + gs1.length]⟩]) (bitsOf n u)).getD (n + gs1.length + 1) false = _
        rw [hstep.2.2.2 (bitsOf n u) (bitsOf_len n u), h1sem u]
        have hm_wire : (wiresOf gs1 (bitsOf n u)).getD m false = decide (u ⟨m, hm⟩ = 1) := by
          rw [wiresOf_getD_lt gs1 (bitsOf n u) (by rw [bitsOf_len]; exact hm)]
          exact bitsOf_getD n u ⟨m, hm⟩
        rw [hm_wire, hsplit, Finset.sum_insert hnotmem, hcm, one_mul, zmod2_add_decide]
        cases (wiresOf gs (bitsOf n u)).getD acc false <;>
          cases decide (u ⟨m, hm⟩ = 1) <;>
          cases decide ((∑ x ∈ Finset.univ.filter (fun j : Fin n => j.val < m), c x * u x) = 1) <;> decide
    · have hcm0 : c ⟨m, hm⟩ = 0 := by
        rcases zmod2_cases (c ⟨m, hm⟩) with h0 | h1
        · exact h0
        · exact absurd h1 hcm
      refine ⟨ext1, ?_, ?_, ?_, ?_, ?_⟩
      · simp [appendAffineLoop, hcm, gs1, h1eq]
      · simpa [appendAffineLoop, hcm, gs1] using h1leg
      · simpa [appendAffineLoop, hcm, gs1] using h1cost
      · simpa [appendAffineLoop, hcm, gs1, acc1] using h1lt
      · intro u
        simp only [appendAffineLoop, hcm, ↓reduceIte]
        rw [h1sem u, hsplit, Finset.sum_insert hnotmem, hcm0, zero_mul, zero_add]

def appendAffine (n : ℕ) (gs : List Gate) (c : Fin n → F2) (b : F2) : List Gate × ℕ :=
  let g0 := if b = 1 then Gate.mk .and [] else Gate.mk .or []
  appendAffineLoop n c n (le_refl n) (gs ++ [g0]) (n + gs.length)

lemma appendAffine_spec (n : ℕ) (gs : List Gate) (c : Fin n → F2) (b : F2) (hgs : legalGates n gs) :
    let res := appendAffine n gs c b
    ∃ ext : List Gate,
      res.1 = gs ++ ext ∧
      legalGates n res.1 ∧
      costGates res.1 = costGates gs ∧
      res.2 < n + res.1.length ∧
      ∀ u : Fin n → F2,
        (wiresOf res.1 (bitsOf n u)).getD res.2 false = decide (dotProduct c u + b = 1) := by
  have hc := appendConst_spec n gs b hgs
  let g0 := if b = 1 then Gate.mk .and [] else Gate.mk .or []
  rcases appendAffineLoop_spec n c n (le_refl n) (gs ++ [g0]) (n + gs.length) hc.1 hc.2.2.1 with
    ⟨ext1, h1eq, h1leg, h1cost, h1lt, h1sem⟩
  refine ⟨[g0] ++ ext1, ?_, h1leg, ?_, h1lt, ?_⟩
  · simpa [appendAffine, g0, List.append_assoc] using h1eq
  · dsimp only [appendAffine]
    rw [h1cost, hc.2.1]
  · intro u
    change (wiresOf (appendAffineLoop n c n (le_refl n) (gs ++ [g0]) (n + gs.length)).1 (bitsOf n u)).getD
        (appendAffineLoop n c n (le_refl n) (gs ++ [g0]) (n + gs.length)).2 false = _
    rw [h1sem u, hc.2.2.2 (bitsOf n u) (bitsOf_len n u)]
    have huniv : Finset.univ.filter (fun j : Fin n => j.val < n) = Finset.univ := by
      ext j; simp [j.isLt]
    rw [huniv]
    change Bool.xor (decide (b = 1)) (decide (dotProduct c u = 1)) = _
    rw [zmod2_add_decide, Bool.xor_comm]

def appendSumProdsLoop (n s : ℕ) (cA cB : Fin s → Fin n → F2) (bA bB : Fin s → F2) :
    (m : ℕ) → m ≤ s → List Gate → ℕ → List Gate × ℕ
  | 0, _, gs, acc => (gs, acc)
  | m + 1, hm, gs, acc =>
    let res1 := appendSumProdsLoop n s cA cB bA bB m (by omega) gs acc
    let gs1 := res1.1
    let acc1 := res1.2
    let resA := appendAffine n gs1 (cA ⟨m, hm⟩) (bA ⟨m, hm⟩)
    let gs2 := resA.1
    let wA := resA.2
    let resB := appendAffine n gs2 (cB ⟨m, hm⟩) (bB ⟨m, hm⟩)
    let gs3 := resB.1
    let wB := resB.2
    let gs4 := gs3 ++ [⟨.and, [wA, wB]⟩]
    let wP := n + gs3.length
    (gs4 ++ [⟨.mod 2, [acc1, wP]⟩, ⟨.not, [n + gs4.length]⟩], n + gs4.length + 1)

lemma appendSumProdsLoop_spec (n s : ℕ) (cA cB : Fin s → Fin n → F2) (bA bB : Fin s → F2) :
    ∀ (m : ℕ) (hm : m ≤ s) (gs : List Gate) (acc : ℕ),
      legalGates n gs → acc < n + gs.length →
      let res := appendSumProdsLoop n s cA cB bA bB m hm gs acc
      ∃ ext : List Gate,
        res.1 = gs ++ ext ∧
        legalGates n res.1 ∧
        costGates res.1 = costGates gs + m ∧
        res.2 < n + res.1.length ∧
        ∀ u : Fin n → F2,
          (wiresOf res.1 (bitsOf n u)).getD res.2 false =
            Bool.xor ((wiresOf gs (bitsOf n u)).getD acc false)
              (decide ((∑ i ∈ Finset.univ.filter (fun i : Fin s => i.val < m),
                (dotProduct (cA i) u + bA i) * (dotProduct (cB i) u + bB i)) = 1)) := by
  intro m
  induction m with
  | zero =>
    intro hm gs acc hleg hacc
    refine ⟨[], by simp [appendSumProdsLoop], hleg, by simp [appendSumProdsLoop], hacc, fun u => ?_⟩
    have hemp : Finset.univ.filter (fun i : Fin s => i.val < 0) = ∅ := by ext i; simp
    simp [appendSumProdsLoop, hemp]
  | succ m ih =>
    intro hm gs acc hleg hacc
    rcases ih (by omega) gs acc hleg hacc with ⟨ext1, h1eq, h1leg, h1cost, h1lt, h1sem⟩
    set res1 := appendSumProdsLoop n s cA cB bA bB m (by omega) gs acc
    set gs1 := res1.1
    set acc1 := res1.2
    rcases appendAffine_spec n gs1 (cA ⟨m, hm⟩) (bA ⟨m, hm⟩) h1leg with ⟨extA, hAeq, hAleg, hAcost, hAlt, hAsem⟩
    set resA := appendAffine n gs1 (cA ⟨m, hm⟩) (bA ⟨m, hm⟩)
    set gs2 := resA.1
    set wA := resA.2
    rcases appendAffine_spec n gs2 (cB ⟨m, hm⟩) (bB ⟨m, hm⟩) hAleg with ⟨extB, hBeq, hBleg, hBcost, hBlt, hBsem⟩
    set resB := appendAffine n gs2 (cB ⟨m, hm⟩) (bB ⟨m, hm⟩)
    set gs3 := resB.1
    set wB := resB.2
    have hwA_lt3 : wA < n + gs3.length := by rw [hBeq, List.length_append]; omega
    set gs4 := gs3 ++ [⟨.and, [wA, wB]⟩]
    set wP := n + gs3.length
    have h4leg : legalGates n gs4 :=
      legalGates_snoc hBleg (fun i hi => by simp at hi; rcases hi with rfl | rfl; exact hwA_lt3; exact hBlt)
        ⟨by simp, Or.inl rfl⟩
    have h4cost : costGates gs4 = costGates gs3 + 1 :=
      costGates_snoc_one gs3 ⟨.and, [wA, wB]⟩ ⟨Or.inl rfl, rfl⟩
    have hacc1_lt4 : acc1 < n + gs4.length := by
      simp only [gs4, hBeq, hAeq, List.length_append, List.length_singleton]; omega
    have hwP_lt4 : wP < n + gs4.length := by simp [gs4, wP]
    have hstep := addXor_step n gs4 acc1 wP h4leg hacc1_lt4 hwP_lt4
    refine ⟨ext1 ++ extA ++ extB ++ [⟨.and, [wA, wB]⟩, ⟨.mod 2, [acc1, wP]⟩, ⟨.not, [n + gs4.length]⟩],
      ?_, ?_, ?_, ?_, ?_⟩
    · simp only [appendSumProdsLoop]
      change gs4 ++ [⟨.mod 2, [acc1, wP]⟩, ⟨.not, [n + gs4.length]⟩] = _
      simp only [gs4, hBeq, hAeq, h1eq, List.append_assoc, List.cons_append, List.nil_append]
    · exact hstep.1
    · change costGates (gs4 ++ [⟨.mod 2, [acc1, wP]⟩, ⟨.not, [n + gs4.length]⟩]) = _
      rw [hstep.2.1, h4cost, hBcost, hAcost, h1cost]; omega
    · change n + gs4.length + 1 < n + (gs4 ++ ([⟨.mod 2, [acc1, wP]⟩, ⟨.not, [n + gs4.length]⟩] : List Gate)).length
      simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · intro u
      change (wiresOf (gs4 ++ [⟨.mod 2, [acc1, wP]⟩, ⟨.not, [n + gs4.length]⟩]) (bitsOf n u)).getD (n + gs4.length + 1) false = _
      rw [hstep.2.2.2 (bitsOf n u) (bitsOf_len n u)]
      have hacc1_eq : (wiresOf gs4 (bitsOf n u)).getD acc1 false = (wiresOf gs1 (bitsOf n u)).getD acc1 false := by
        have hgs4_eq : gs4 = gs1 ++ (extA ++ extB ++ [⟨.and, [wA, wB]⟩]) := by
          simp only [gs4, hBeq, hAeq, List.append_assoc]
        rw [hgs4_eq, wiresOf_append_getD_lt gs1 _ (bitsOf n u) (by rw [bitsOf_len]; exact h1lt)]
      have hwP_eq : (wiresOf gs4 (bitsOf n u)).getD wP false =
          decide ((dotProduct (cA ⟨m, hm⟩) u + bA ⟨m, hm⟩) * (dotProduct (cB ⟨m, hm⟩) u + bB ⟨m, hm⟩) = 1) := by
        change (wiresOf (gs3 ++ [⟨.and, [wA, wB]⟩]) (bitsOf n u)).getD (n + gs3.length) false = _
        rw [wiresOf_snoc_last_eq gs3 ⟨.and, [wA, wB]⟩ (bitsOf n u) (bitsOf_len n u)]
        simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
        have hwA_val : (wiresOf gs3 (bitsOf n u)).getD wA false = decide (dotProduct (cA ⟨m, hm⟩) u + bA ⟨m, hm⟩ = 1) := by
          rw [hBeq, wiresOf_append_getD_lt gs2 extB (bitsOf n u) (by rw [bitsOf_len]; exact hAlt)]
          exact hAsem u
        rw [hwA_val, hBsem u, zmod2_mul_decide]
      rw [hacc1_eq, h1sem u, hwP_eq]
      have hsplit : (Finset.univ.filter (fun i : Fin s => i.val < m + 1)) =
          insert ⟨m, hm⟩ (Finset.univ.filter (fun i : Fin s => i.val < m)) := by
        ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
        omega
      have hnotmem : (⟨m, hm⟩ : Fin s) ∉ Finset.univ.filter (fun i : Fin s => i.val < m) := by simp
      rw [hsplit, Finset.sum_insert hnotmem, zmod2_add_decide]
      cases (wiresOf gs (bitsOf n u)).getD acc false <;>
        cases decide ((dotProduct (cA ⟨m, hm⟩) u + bA ⟨m, hm⟩) * (dotProduct (cB ⟨m, hm⟩) u + bB ⟨m, hm⟩) = 1) <;>
        cases decide ((∑ x ∈ Finset.univ.filter (fun i : Fin s => i.val < m),
          (dotProduct (cA x) u + bA x) * (dotProduct (cB x) u + bB x)) = 1) <;> decide

lemma build_sum_prods_circuit (n s : ℕ) (c0 : Fin n → F2) (b0 : F2)
    (cA cB : Fin s → Fin n → F2) (bA bB : Fin s → F2) :
    ∃ C : Circuit, legalGates n C.gates ∧ costGates C.gates = s ∧
      ∀ u : Fin n → F2, C.eval (bitsOf n u) =
        decide ((dotProduct c0 u + b0) +
          ∑ i : Fin s, (dotProduct (cA i) u + bA i) * (dotProduct (cB i) u + bB i) = 1) := by
  have hnil : legalGates n [] := ⟨fun j hj => by simp at hj, fun h hh => by simp at hh⟩
  rcases appendAffine_spec n [] c0 b0 hnil with ⟨_, _, h0leg, h0cost, h0lt, h0sem⟩
  set res0 := appendAffine n [] c0 b0
  rcases appendSumProdsLoop_spec n s cA cB bA bB s (le_refl s) res0.1 res0.2 h0leg h0lt with
    ⟨_, _, hleg, hcost, _, hsem⟩
  set res := appendSumProdsLoop n s cA cB bA bB s (le_refl s) res0.1 res0.2
  refine ⟨⟨res.1, res.2⟩, hleg, ?_, fun u => ?_⟩
  · have hc0 : costGates ([] : List Gate) = 0 := by simp [costGates]
    dsimp only [res, res0] at hcost h0cost ⊢
    omega
  · change (wiresOf res.1 (bitsOf n u)).getD res.2 false = _
    rw [hsem u, h0sem u]
    have huniv : Finset.univ.filter (fun i : Fin s => i.val < s) = Finset.univ := by
      ext i; simp
    rw [huniv, ← zmod2_add_decide]

def signBool (b : Bool) : ℤ := if b then -1 else 1

lemma signBool_xor (a b : Bool) : signBool (Bool.xor a b) = signBool a * signBool b := by
  cases a <;> cases b <;> rfl

lemma agree_eq_sign (b1 b2 b3 : Bool) :
    (if b1 = Bool.xor b2 b3 then (1 : ℤ) else -1) = signBool (Bool.xor b1 b2) * signBool b3 := by
  cases b1 <;> cases b2 <;> cases b3 <;> rfl

lemma eq_f2_sign (a b : F2) :
    (if a = b then (1 : ℤ) else -1) = signBool (decide (a = 1)) * signBool (decide (b = 1)) := by
  fin_cases a <;> fin_cases b <;> decide

lemma signBool_abs_one (b : Bool) : |signBool b| = 1 := by
  cases b <;> simp [signBool]

lemma sum_sign_dot_univ {k : ℕ} (w : Fin k → F2) (hw : w ≠ 0) :
    (∑ x : Fin k → F2, signBool (decide (dotProduct w x = 1))) = 0 := by
  have hex : ∃ j : Fin k, w j = 1 := by
    by_contra hnot; push Not at hnot
    apply hw; funext j
    rcases zmod2_cases (w j) with h0 | h1
    · exact h0
    · exact absurd h1 (hnot j)
  rcases hex with ⟨j, hj⟩
  let u0 : Fin k → F2 := Pi.single j 1
  have hdot : dotProduct w u0 = 1 := by
    simp [u0, dotProduct_single, hj]
  let e : (Fin k → F2) ≃ (Fin k → F2) :=
    { toFun := fun x => x + u0
      invFun := fun x => x + u0
      left_inv := fun x => by dsimp only; rw [add_assoc, zmod2_vec_add_self, add_zero]
      right_inv := fun x => by dsimp only; rw [add_assoc, zmod2_vec_add_self, add_zero] }
  set S := ∑ x : Fin k → F2, signBool (decide (dotProduct w x = 1))
  have hS : S = -S := by
    calc S = ∑ x : Fin k → F2, signBool (decide (dotProduct w (e x) = 1)) :=
          (Equiv.sum_comp e (fun x => signBool (decide (dotProduct w x = 1)))).symm
      _ = ∑ x : Fin k → F2, -signBool (decide (dotProduct w x = 1)) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          show signBool (decide (dotProduct w (x + u0) = 1)) = _
          rw [dotProduct_add, hdot, zmod2_add_decide]
          cases decide (dotProduct w x = 1) <;> rfl
      _ = -S := by rw [Finset.sum_neg_distrib]
  omega

lemma vec_eq_sum_single {k : ℕ} (v : Fin k → F2) :
    v = ∑ i : Fin k, v i • Pi.single i (1 : F2) := by
  funext j
  simp [Finset.sum_apply, Pi.single_apply]

def concatVec {k : ℕ} (x y : Fin k → F2) : Fin (2 * k) → F2 :=
  fun idx => if h : idx.val < k then x ⟨idx.val, h⟩ else y ⟨idx.val - k, by omega⟩

lemma bitsOf_concatVec {k : ℕ} (x y : Fin k → F2) :
    bitsOf k x ++ bitsOf k y = bitsOf (2 * k) (concatVec x y) := by
  apply List.ext_getElem
  · simp [bitsOf_len]; omega
  · intro i h1 h2
    simp only [bitsOf]
    by_cases hik : i < k
    · rw [List.getElem_append_left (by simp; exact hik)]
      simp [concatVec, hik]
    · rw [List.getElem_append_right (by simp; omega)]
      simp [concatVec, hik]

lemma dotProduct_concatVec {k : ℕ} (u v x y : Fin k → F2) :
    dotProduct (concatVec u v) (concatVec x y) = dotProduct u x + dotProduct v y := by
  simp only [dotProduct]
  let e : Fin k ⊕ Fin k ≃ Fin (2 * k) :=
    { toFun := Sum.elim (fun i => ⟨i.val, by omega⟩) (fun i => ⟨k + i.val, by omega⟩)
      invFun := fun i => if h : i.val < k then Sum.inl ⟨i.val, h⟩ else Sum.inr ⟨i.val - k, by omega⟩
      left_inv := fun s => by
        cases s with
        | inl i => simp [i.isLt]
        | inr i =>
          have hnot : ¬ (k + i.val < k) := by omega
          simp [hnot]
      right_inv := fun i => by
        by_cases h : i.val < k
        · simp [h]
        · simp only [h, ↓reduceDIte, Sum.elim_inr]
          apply Fin.ext; dsimp; omega }
  rw [← Equiv.sum_comp e, Fintype.sum_sum_type]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp [e, concatVec, i.isLt]
  · refine Finset.sum_congr rfl fun i _ => ?_
    have hnot : ¬ (k + i.val < k) := by omega
    simp [e, concatVec, hnot]

lemma linear_map_left_inv {k s : ℕ} (B : (Fin s → F2) →ₗ[F2] (Fin k → F2))
    (hB : Function.Injective B) :
    ∃ L : (Fin k → F2) →ₗ[F2] (Fin s → F2), ∀ v : Fin s → F2, L (B v) = v := by
  obtain ⟨V', hcompl⟩ := Submodule.exists_isCompl (LinearMap.range B)
  let π : (Fin k → F2) →ₗ[F2] LinearMap.range B := Submodule.linearProjOfIsCompl (LinearMap.range B) V' hcompl
  let e : (Fin s → F2) ≃ₗ[F2] LinearMap.range B := LinearEquiv.ofInjective B hB
  refine ⟨e.symm.toLinearMap.comp π, fun v => ?_⟩
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  have hmem : B v ∈ LinearMap.range B := ⟨v, rfl⟩
  have hpi : π (B v) = ⟨B v, hmem⟩ := Submodule.linearProjOfIsCompl_apply_left hcompl ⟨B v, hmem⟩
  rw [hpi]
  have hev : e v = ⟨B v, hmem⟩ := rfl
  rw [← hev, LinearEquiv.symm_apply_apply]

lemma linear_coord_dot {k : ℕ} (ℓ : (Fin k → F2) →ₗ[F2] F2) :
    ∃ r : Fin k → F2, ∀ y : Fin k → F2, ℓ y = dotProduct r y := by
  refine ⟨fun j => ℓ (Pi.single j 1), fun y => ?_⟩
  conv_lhs => rw [vec_eq_sum_single y, map_sum]
  simp only [dotProduct, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ => by ring

lemma build_sum_prods_bounded (n s : ℕ) (c0 : Fin n → F2) (b0 : F2)
    (cA cB : Fin s → Fin n → F2) (bA bB : Fin s → F2) :
    ∃ C : Circuit, legalGates n C.gates ∧ costGates C.gates = s ∧
      C.output < n + C.gates.length ∧
      ∀ u : Fin n → F2, C.eval (bitsOf n u) =
        decide ((dotProduct c0 u + b0) +
          ∑ i : Fin s, (dotProduct (cA i) u + bA i) *
            (dotProduct (cB i) u + bB i) = 1) := by
  have hnil : legalGates n [] := ⟨fun j hj => by simp at hj, by simp⟩
  rcases appendAffine_spec n [] c0 b0 hnil with
    ⟨_, _, h0leg, h0cost, h0lt, h0sem⟩
  set res0 := appendAffine n [] c0 b0
  rcases appendSumProdsLoop_spec n s cA cB bA bB s (le_refl s)
      res0.1 res0.2 h0leg h0lt with
    ⟨_, _, hleg, hcost, hout, hsem⟩
  set res := appendSumProdsLoop n s cA cB bA bB s (le_refl s) res0.1 res0.2
  refine ⟨⟨res.1, res.2⟩, hleg, ?_, hout, fun u => ?_⟩
  · have hc0 : costGates ([] : List Gate) = 0 := by simp [costGates]
    dsimp only [res, res0] at hcost h0cost ⊢
    omega
  · change (wiresOf res.1 (bitsOf n u)).getD res.2 false = _
    rw [hsem u, h0sem u]
    have huniv : Finset.univ.filter (fun i : Fin s => i.val < s) = Finset.univ := by
      ext i; simp
    rw [huniv, ← zmod2_add_decide]

lemma legalGates_append {n : ℕ} {gs hs : List Gate}
    (hg : legalGates n gs) (hh : legalGates (n + gs.length) hs) :
    legalGates n (gs ++ hs) := by
  refine ⟨readsBack_append hg.1 hh.1, ?_⟩
  intro g h
  rcases List.mem_append.mp h with h | h
  · exact hg.2 g h
  · exact hh.2 g h

lemma bitsOf_decode (n : ℕ) (w : List Bool) (hw : w.length = n) :
    bitsOf n (fun i => if w.getD i.val false then (1 : F2) else 0) = w := by
  subst n
  apply List.ext_getElem
  · simp [bitsOf_len]
  · intro i h1 h2
    simp only [bitsOf, List.getElem_ofFn, zmod2_bool_decide]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

lemma dotProduct_append_zero (n t : ℕ) (c : Fin n → F2) (z : Fin (n+t) → F2) :
    dotProduct (Fin.append c 0) z = dotProduct c (fun i => z (Fin.castAdd t i)) := by
  simp [dotProduct, Fin.sum_univ_add]

lemma build_cubic_prods (n s : ℕ) (c0 : Fin n → F2) (b0 : F2)
    (cA cB : Fin s → Fin n → F2) (bA bB coeff : Fin s → F2)
    (u v : Fin n → F2) (u0 v0 : F2) :
    ∃ C : Circuit, legalGates n C.gates ∧ costGates C.gates = s+1 ∧
      ∀ x : Fin n → F2, C.eval (bitsOf n x) = decide
        (dotProduct c0 x + b0 +
          ∑ i : Fin s, (dotProduct (cA i) x + bA i) *
            (dotProduct (cB i) x + bB i +
              coeff i * ((dotProduct u x + u0) * (dotProduct v x + v0))) = 1) := by
  classical
  obtain ⟨P, hP, hcP, hoP, heP⟩ := build_sum_prods_bounded n 1 0 0
    (fun _ => u) (fun _ => v) (fun _ => u0) (fun _ => v0)
  have heP' (x : Fin n → F2) : P.eval (bitsOf n x) =
      decide ((dotProduct u x + u0) * (dotProduct v x + v0) = 1) := by
    simpa using heP x
  let N := n + P.gates.length
  let p : Fin N := ⟨P.output, hoP⟩
  let lift : (Fin n → F2) → (Fin N → F2) := fun c => Fin.append c 0
  obtain ⟨D, hD, hcD, _, heD⟩ := build_sum_prods_bounded N s (lift c0) b0
    (fun i => lift (cA i))
    (fun i => lift (cB i) + Pi.single p (coeff i)) bA bB
  refine ⟨⟨P.gates ++ D.gates, D.output⟩, legalGates_append hP hD, ?_, ?_⟩
  · change costGates (P.gates ++ D.gates) = s+1
    rw [costGates_append, hcP, hcD]
    omega
  · intro x
    let w := P.wires (bitsOf n x)
    have hw : w.length = N := by
      exact (wiresOf_len P.gates (bitsOf n x)).trans (by rw [bitsOf_len])
    let z : Fin N → F2 := fun j => if w.getD j.val false then 1 else 0
    have hz : bitsOf N z = w := bitsOf_decode N w hw
    have hinput (i : Fin n) : z (Fin.castAdd P.gates.length i) = x i := by
      dsimp only [z, w]
      change (if (wiresOf P.gates (bitsOf n x)).getD i.val false then (1 : F2) else 0) = x i
      rw [wiresOf_getD_lt _ _ (by rw [bitsOf_len]; exact i.isLt), bitsOf_getD]
      exact zmod2_decide_bool (x i)
    have hdot (c : Fin n → F2) : dotProduct (lift c) z = dotProduct c x := by
      rw [show lift c = Fin.append c 0 from rfl, dotProduct_append_zero]
      simp only [hinput]
    have hp : z p = (dotProduct u x + u0) * (dotProduct v x + v0) := by
      dsimp only [z, p, w]
      change (if P.eval (bitsOf n x) then (1 : F2) else 0) = _
      rw [heP']
      exact zmod2_decide_bool _
    have heval : (Circuit.mk (P.gates ++ D.gates) D.output).eval (bitsOf n x) =
        D.eval (bitsOf N z) := by
      rw [hz]
      exact congrArg (fun l : List Bool => l.getD D.output false)
        (wiresOf_append P.gates D.gates (bitsOf n x))
    rw [heval, heD, hdot]
    congr 1
    congr 1
    apply congrArg (fun a => dotProduct c0 x + b0 + a)
    apply Finset.sum_congr rfl
    intro i _
    rw [hdot, add_dotProduct, hdot, single_dotProduct, hp]
    ring

lemma raw_projection {k s : ℕ} (g : (Fin k → F2) → F2)
    (B : (Fin s → F2) →ₗ[F2] (Fin k → F2)) (a : Fin k → F2)
    (q : (Fin s → F2) → F2) (L : (Fin k → F2) →ₗ[F2] (Fin s → F2))
    (hB : Function.Injective B) (hLB : ∀ v, L (B v) = v) (C : Circuit)
    (hCe : ∀ x y : Fin k → F2,
      C.eval (bitsOf k x ++ bitsOf k y) =
        decide (dotProduct x (a+B (L (y+a))) + q (L (y+a)) = 1)) : (∑ x : Fin k → F2, ∑ y : Fin k → F2,
    if C.eval (bitsOf k x ++ bitsOf k y) = decide (dotProduct x y + g y = 1)
    then (1 : ℤ) else -1) =
    (2 : ℤ) ^ k * ∑ v : Fin s → F2, if g (a + B v) = q v then (1 : ℤ) else -1 := by
  classical
  rw [Finset.sum_comm]
  have hinner : ∀ y : Fin k → F2,
      (∑ x : Fin k → F2, if C.eval (bitsOf k x ++ bitsOf k y) = decide (dotProduct x y + g y = 1)
        then (1 : ℤ) else -1) =
      if y + a ∈ LinearMap.range B then
        (2 : ℤ) ^ k * (if g y = q (L (y + a)) then (1 : ℤ) else -1)
      else 0 := by
    intro y
    have hrw : ∀ x : Fin k → F2,
        (if C.eval (bitsOf k x ++ bitsOf k y) = decide (dotProduct x y + g y = 1) then (1 : ℤ) else -1) =
        signBool (decide (dotProduct (a + B (L (y + a)) + y) x = 1)) *
          (if g y = q (L (y + a)) then (1 : ℤ) else -1) := by
      intro x
      rw [hCe x y, zmod2_add_decide (dotProduct x y) (g y), agree_eq_sign, eq_f2_sign]
      have hxor : Bool.xor (decide (dotProduct x (a + B (L (y + a))) + q (L (y + a)) = 1)) (decide (dotProduct x y = 1)) =
          Bool.xor (decide (dotProduct (a + B (L (y + a)) + y) x = 1)) (decide (q (L (y + a)) = 1)) := by
        rw [← zmod2_add_decide, ← zmod2_add_decide, add_dotProduct, dotProduct_comm (a + B (L (y + a))) x,
            dotProduct_comm y x]
        congr 1; ring
      rw [hxor, signBool_xor]
      ring
    simp_rw [hrw, ← Finset.sum_mul]
    by_cases hmem : y + a ∈ LinearMap.range B
    · simp only [hmem, ↓reduceIte]
      rcases hmem with ⟨v, hv⟩
      have hzero : a + B (L (y + a)) + y = 0 := by
        rw [← hv, hLB v, hv]
        calc a + (y + a) + y = (a + a) + (y + y) := by abel
          _ = 0 := by rw [zmod2_vec_add_self, zmod2_vec_add_self, add_zero]
      simp only [hzero, zero_dotProduct]
      have hcard : (∑ _x : Fin k → F2, signBool (decide ((0 : F2) = 1))) = (2 : ℤ) ^ k := by
        change (∑ _x : Fin k → F2, (1 : ℤ)) = (2 : ℤ) ^ k
        simp [ZMod.card]
      rw [hcard]
    · simp only [hmem, ↓reduceIte]
      have hne : a + B (L (y + a)) + y ≠ 0 := by
        intro h0
        apply hmem
        refine ⟨L (y + a), ?_⟩
        have h1 : B (L (y + a)) + (a + B (L (y + a)) + y) = y + a := by
          calc B (L (y + a)) + (a + B (L (y + a)) + y)
              = (B (L (y + a)) + B (L (y + a))) + (y + a) := by abel
            _ = y + a := by rw [zmod2_vec_add_self, zero_add]
        rw [h0, add_zero] at h1
        exact h1
      rw [sum_sign_dot_univ _ hne, zero_mul]
  simp_rw [hinner]
  rw [← Finset.sum_filter]
  let f_inj : (Fin s → F2) → (Fin k → F2) := fun v => a + B v
  have hbij : Finset.univ.image f_inj = Finset.univ.filter (fun y : Fin k → F2 => y + a ∈ LinearMap.range B) := by
    ext y
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter, f_inj]
    constructor
    · rintro ⟨v, rfl⟩
      refine ⟨v, ?_⟩
      calc B v = (a + a) + B v := by rw [zmod2_vec_add_self, zero_add]
        _ = a + B v + a := by abel
    · rintro ⟨v, hv⟩
      refine ⟨v, ?_⟩
      calc a + B v = a + (y + a) := by rw [hv]
        _ = (a + a) + y := by abel
        _ = y := by rw [zmod2_vec_add_self, zero_add]
  rw [← hbij, Finset.sum_image (fun v1 _ v2 _ h => hB (add_left_cancel h)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  have harg : f_inj v + a = B v := by
    dsimp only [f_inj]
    calc a + B v + a = (a + a) + B v := by abel
      _ = B v := by rw [zmod2_vec_add_self, zero_add]
  rw [harg, hLB v]

lemma build_projection_triple {n s : ℕ}
    (B : (Fin s → F2) →ₗ[F2] (Fin n → F2)) (hB : Function.Injective B)
    (α β γ : (Fin s → F2) →ₗ[F2] F2) (c z : F2) (g : (Fin n → F2) → F2) :
    ∃ C : Circuit, legalGates (2*n) C.gates ∧ costGates C.gates = s+1 ∧
      (∑ x : Fin n → F2, ∑ y : Fin n → F2,
        if C.eval (bitsOf n x ++ bitsOf n y) = decide (dotProduct x y + g y = 1)
        then (1 : ℤ) else -1).natAbs =
      2^n * (∑ t : Fin s → F2,
        if g (B t) = c * α t + z + α t * β t * γ t then (1 : ℤ) else -1).natAbs := by
  classical
  obtain ⟨L, hLB⟩ := linear_map_left_inv B hB
  have hcoord : ∀ a : Fin s, ∃ r : Fin n → F2, ∀ y, L y a = dotProduct r y :=
    fun a => linear_coord_dot ((LinearMap.proj a).comp L)
  choose rv hrv using hcoord
  obtain ⟨ca, hca⟩ := linear_coord_dot α
  obtain ⟨ra, hra⟩ := linear_coord_dot (α.comp L)
  obtain ⟨rb, hrb⟩ := linear_coord_dot (β.comp L)
  obtain ⟨rc, hrc⟩ := linear_coord_dot (γ.comp L)
  change ∀ y, α (L y) = dotProduct ra y at hra
  change ∀ y, β (L y) = dotProduct rb y at hrb
  change ∀ y, γ (L y) = dotProduct rc y at hrc
  obtain ⟨C, hC, hcC, heC⟩ := build_cubic_prods (2*n) s
    (concatVec 0 (c • ra)) z
    (fun a => concatVec 0 (rv a))
    (fun a => concatVec (B (Pi.single a 1)) 0)
    0 0 ca (concatVec 0 rb) (concatVec 0 rc) 0 0
  refine ⟨C, hC, hcC, ?_⟩
  have hCe (x y : Fin n → F2) :
      C.eval (bitsOf n x ++ bitsOf n y) =
        decide (dotProduct x (0 + B (L (y+0))) +
          (c * α (L (y+0)) + z + α (L (y+0)) * β (L (y+0)) * γ (L (y+0))) = 1) := by
    rw [bitsOf_concatVec, heC]
    simp only [dotProduct_concatVec, zero_dotProduct, dotProduct_zero, zero_add, add_zero, Pi.zero_apply, smul_dotProduct, smul_eq_mul, ← hrv, ← hra, ← hrb, ← hrc]
    congr 1
    congr 1
    have hdot : (∑ a : Fin s, L y a * dotProduct (B (Pi.single a 1)) x) =
        dotProduct x (B (L y)) := by
      conv_rhs => rw [vec_eq_sum_single (L y), map_sum, dotProduct_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [map_smul, dotProduct_smul, smul_eq_mul, dotProduct_comm]
    have hprod : (∑ a : Fin s, L y a * (ca a * (β (L y) * γ (L y)))) =
        α (L y) * β (L y) * γ (L y) := by
      rw [hca]
      simp only [dotProduct, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      ring
    simp_rw [mul_add, Finset.sum_add_distrib]
    rw [hdot, hprod]
    ring
  have hraw := raw_projection g B 0
    (fun t => c*α t+z+α t*β t*γ t) L hB hLB C hCe
  simp only [zero_add] at hraw
  rw [hraw, Int.natAbs_mul, Int.natAbs_pow]
  rfl

end PEqualNP.Outside.L_meta_32057_aux.LineCircuit


namespace PEqualNP.Outside.L_meta_32057_aux.LineBias

abbrev F := ZMod 2

def chi (a : F) : ℤ := if a = 0 then 1 else -1

lemma chi_add (a b : F) : chi (a + b) = chi a * chi b := by
  fin_cases a <;> fin_cases b <;> rfl

lemma chi_sum {α : Type*} (s : Finset α) (f : α → F) :
    chi (∑ i ∈ s, f i) = ∏ i ∈ s, chi (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [chi]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, chi_add, ih]

lemma sum_uv_factor {m : ℕ} (h : Fin m → F) :
    (∑ u : Fin m → F, ∑ v : Fin m → F,
      chi (∑ j : Fin m, h j * u j * v j)) =
    ∏ j : Fin m, ∑ p : F × F, chi (h j * p.1 * p.2) := by
  let G : Fin m → F × F → ℤ := fun j p => chi (h j * p.1 * p.2)
  have hps : (∏ j : Fin m, ∑ p : F × F, G j p) =
      ∑ f : Fin m → F × F, ∏ j : Fin m, G j (f j) := Fintype.prod_sum G
  rw [hps]
  let ePair : ((Fin m → F) × (Fin m → F)) ≃ (Fin m → F × F) :=
    { toFun := fun p j => (p.1 j, p.2 j)
      invFun := fun f => (fun j => (f j).1, fun j => (f j).2)
      left_inv := fun ⟨_, _⟩ => rfl
      right_inv := fun _ => rfl }
  rw [← Fintype.sum_prod_type', ← ePair.sum_comp]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [chi_sum]
  rfl

lemma two_bit_exact (c : F) :
    (∑ p : F × F, chi (c * p.1 * p.2)) = if c ≠ 0 then 2 else 4 := by
  fin_cases c <;> decide

lemma prod_two_four {α : Type*} (s : Finset α) (P : α → Prop) [DecidablePred P] :
    (∏ i ∈ s, if P i then (2 : ℤ) else 4) =
      2 ^ (2 * s.card - (s.filter P).card) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hle : (s.filter P).card ≤ s.card := Finset.card_filter_le _ _
    have hnot : a ∉ s.filter P := fun h => ha (Finset.mem_filter.mp h).1
    by_cases hp : P a
    · rw [Finset.prod_insert ha, ite_eq_left hp, Finset.card_insert_of_notMem ha,
        Finset.filter_insert, ite_eq_left hp, Finset.card_insert_of_notMem hnot, ih]
      rw [show 2 * (s.card + 1) - ((s.filter P).card + 1) =
        (2 * s.card - (s.filter P).card) + 1 by omega, pow_succ]
      ring
    · rw [Finset.prod_insert ha, ite_eq_right hp, Finset.card_insert_of_notMem ha,
        Finset.filter_insert, ite_eq_right hp, ih]
      rw [show 2 * (s.card + 1) - (s.filter P).card =
        (2 * s.card - (s.filter P).card) + 2 by omega, pow_add]
      ring

lemma sum_uv_exact {m : ℕ} (c : Fin m → F) :
    (∑ u : Fin m → F, ∑ v : Fin m → F,
      chi (∑ i : Fin m, c i * u i * v i)) =
      2 ^ (2 * m - ((Finset.univ : Finset (Fin m)).filter (fun i => c i ≠ 0)).card) := by
  rw [sum_uv_factor]
  simp_rw [two_bit_exact]
  simpa using prod_two_four (Finset.univ : Finset (Fin m)) (fun i => c i ≠ 0)

lemma sum_selector_exact {m : ℕ} (c : Fin m → F) :
    (∑ t : F, ∑ u : Fin m → F, ∑ v : Fin m → F,
      chi (t * ∑ i : Fin m, c i * u i * v i)) =
      2 ^ (2 * m) +
        2 ^ (2 * m - ((Finset.univ : Finset (Fin m)).filter (fun i => c i ≠ 0)).card) := by
  have htwo (f : F → ℤ) : ∑ t : F, f t = f 0 + f 1 := Fin.sum_univ_two f
  rw [htwo]
  simp only [zero_mul, one_mul]
  rw [sum_uv_exact]
  simp [chi, ZMod.card, pow_add, two_mul]

lemma sum_selector_padded {m r : ℕ} (c : Fin m → F) :
    (∑ t : F, ∑ u : Fin m → F, ∑ v : Fin m → F, ∑ _z : Fin r → F,
      chi (t * ∑ i : Fin m, c i * u i * v i)) =
      2 ^ r * (2 ^ (2 * m) +
        2 ^ (2 * m - ((Finset.univ : Finset (Fin m)).filter (fun i => c i ≠ 0)).card)) := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, ZMod.card,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  simp_rw [← Finset.mul_sum]
  rw [sum_selector_exact]

lemma cancel_weight {m : ℕ} (c : Fin m → F) (i₀ : Fin m) (hi : c i₀ ≠ 0) :
    ((Finset.univ : Finset (Fin m)).filter
      (fun i => Function.update c i₀ 0 i ≠ 0)).card + 1 =
      ((Finset.univ : Finset (Fin m)).filter (fun i => c i ≠ 0)).card := by
  classical
  have heq : (Finset.univ : Finset (Fin m)).filter
      (fun i => Function.update c i₀ 0 i ≠ 0) =
      ((Finset.univ : Finset (Fin m)).filter (fun i => c i ≠ 0)).erase i₀ := by
    ext i
    by_cases h : i = i₀
    · subst i
      simp
    · simp [h]
  rw [heq]
  exact Finset.card_erase_add_one (by simp [hi])

lemma sum_selector_cancelled {m d r : ℕ} (c : Fin m → F) (i₀ : Fin m)
    (hi : c i₀ ≠ 0)
    (hw : ((Finset.univ : Finset (Fin m)).filter (fun i => c i ≠ 0)).card = d) :
    (∑ t : F, ∑ u : Fin m → F, ∑ v : Fin m → F, ∑ _z : Fin r → F,
      chi (t * ∑ i : Fin m, Function.update c i₀ 0 i * u i * v i)) =
      2 ^ r * (2 ^ (2 * m) + 2 ^ (2 * m + 1 - d)) := by
  rw [sum_selector_padded]
  have hcard := cancel_weight c i₀ hi
  have hle : d ≤ m := by
    rw [← hw]
    exact (Finset.card_filter_le _ _).trans_eq (by simp)
  rw [hw] at hcard
  have hex : 2 * m - ((Finset.univ : Finset (Fin m)).filter
      (fun i => Function.update c i₀ 0 i ≠ 0)).card = 2 * m + 1 - d := by omega
  rw [hex]

lemma scaled_line_value (m r d : ℕ) (hd : d ≤ m) :
    2 ^ (m + 2) * (2 ^ r * (2 ^ (2 * m) + 2 ^ (2 * m + 1 - d))) =
      2 ^ (2 * m + r + 2) * (2 ^ m + 2 ^ (m + 1 - d)) := by
  rw [show 2 * m + 1 - d = m + (m + 1 - d) by omega]
  simp only [two_mul, pow_add]
  ring

lemma cancelled_line_exact {m d r : ℕ} (c : Fin m → F) (i₀ : Fin m)
    (hi : c i₀ ≠ 0)
    (hw : ((Finset.univ : Finset (Fin m)).filter (fun i => c i ≠ 0)).card = d) :
    2 ^ (m + 2) *
      (∑ t : F, ∑ u : Fin m → F, ∑ v : Fin m → F, ∑ _z : Fin r → F,
        chi (t * ∑ i : Fin m, Function.update c i₀ 0 i * u i * v i)).natAbs =
      2 ^ (2 * m + r + 2) * (2 ^ m + 2 ^ (m + 1 - d)) := by
  rw [sum_selector_cancelled c i₀ hi hw]
  have habs : (2 ^ r * (2 ^ (2 * m) + 2 ^ (2 * m + 1 - d)) : ℤ).natAbs =
      2 ^ r * (2 ^ (2 * m) + 2 ^ (2 * m + 1 - d)) := by norm_cast
  rw [habs]
  apply scaled_line_value
  rw [← hw]
  exact (Finset.card_filter_le _ _).trans_eq (by simp)

lemma f2_add_self (a : F) : a + a = 0 := by fin_cases a <;> rfl

lemma f2_cases (a : F) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma cancel_polynomial {m : ℕ} (c u v : Fin m → F) (i₀ : Fin m) :
    (∑ i : Fin m, Function.update c i₀ 0 i * u i * v i) =
      (∑ i : Fin m, c i * u i * v i) + c i₀ * u i₀ * v i₀ := by
  classical
  have heq : (fun i => Function.update c i₀ 0 i * u i * v i) =
      fun i => c i * u i * v i +
        if i = i₀ then c i₀ * u i₀ * v i₀ else 0 := by
    funext i
    by_cases h : i = i₀
    · subst i
      simp only [Function.update_self, zero_mul, ite_true, f2_add_self]
    · simp [h]
  rw [heq, Finset.sum_add_distrib, Finset.sum_ite_eq',
    ite_eq_left (Finset.mem_univ i₀)]

lemma cancel_active_polynomial {m : ℕ} (c u v : Fin m → F) (i₀ : Fin m)
    (hi : c i₀ ≠ 0) :
    (∑ i : Fin m, Function.update c i₀ 0 i * u i * v i) =
      (∑ i : Fin m, c i * u i * v i) + u i₀ * v i₀ := by
  have hval : c i₀ = 1 := by
    rcases f2_cases (c i₀) with h | h
    · exact False.elim (hi h)
    · exact h
  rw [cancel_polynomial, hval, one_mul]

lemma one_variable_affine (h : F → F) (t : F) :
    h t = h 0 + (h 1 + h 0) * t := by
  rcases f2_cases t with rfl | rfl
  · simp
  · simp only [mul_one]
    rw [add_left_comm, f2_add_self, add_zero]

end PEqualNP.Outside.L_meta_32057_aux.LineBias

namespace PEqualNP.Outside.L_meta_32057_aux.LineAttainment

open LineBias

abbrev Data (m r : ℕ) := (Fin m → F) × ((Fin m → F) × (Fin r → F))
abbrev Coordinates (m r : ℕ) := F × Data m r
abbrev E (m r : ℕ) := Fin (2 * m + r + 1) → F
abbrev S (k : ℕ) := Fin k → F
abbrev V (k m r : ℕ) := Fin (k + 2 * m + r) → F

noncomputable def chart (m r : ℕ) : E m r ≃ₗ[F] Coordinates m r :=
  LinearEquiv.ofFinrankEq _ _ (by
    simp only [E, Coordinates, Data, Module.finrank_pi, Module.finrank_self,
      Fintype.card_fin, Module.finrank_prod]
    omega)

def selectorLine {k m r : ℕ} (a : S k) : Coordinates m r →ₗ[F] S k × Data m r where
  toFun p := (p.1 • a, p.2)
  map_add' p q := by
    apply Prod.ext
    · exact add_smul _ _ _
    · rfl
  map_smul' c p := by
    apply Prod.ext
    · exact mul_smul _ _ _
    · rfl

lemma selectorLine_injective {k m r : ℕ} {a : S k} (ha : a ≠ 0) :
    Function.Injective (selectorLine (m := m) (r := r) a) := by
  intro p q heq
  have hscalar : p.1 • a = q.1 • a := congrArg Prod.fst heq
  have hdata : p.2 = q.2 := congrArg (fun z : S k × Data m r => z.2) heq
  apply Prod.ext _ hdata
  rcases f2_cases p.1 with hp | hp <;> rcases f2_cases q.1 with hq | hq
  · exact hp.trans hq.symm
  · exfalso
    exact ha (by simpa [hp, hq] using hscalar.symm)
  · exfalso
    exact ha (by simpa [hp, hq] using hscalar)
  · exact hp.trans hq.symm

noncomputable def embedding {k m r : ℕ}
    (e : V k m r ≃ₗ[F] S k × Data m r) (a : S k) : E m r →ₗ[F] V k m r :=
  e.symm.toLinearMap.comp ((selectorLine a).comp (chart m r).toLinearMap)

lemma embedding_injective {k m r : ℕ}
    (e : V k m r ≃ₗ[F] S k × Data m r) {a : S k} (ha : a ≠ 0) :
    Function.Injective (embedding e a) :=
  e.symm.injective.comp ((selectorLine_injective ha).comp (chart m r).injective)

lemma embedding_coordinates {k m r : ℕ}
    (e : V k m r ≃ₗ[F] S k × Data m r) (a : S k) (x : E m r) :
    e (embedding e a x) = ((chart m r x).1 • a, (chart m r x).2) := by
  simp [embedding, selectorLine]

noncomputable def alpha (m r : ℕ) : E m r →ₗ[F] F :=
  (LinearMap.fst F F (Data m r)).comp (chart m r).toLinearMap

noncomputable def beta {m r : ℕ} (i₀ : Fin m) : E m r →ₗ[F] F where
  toFun x := (chart m r x).2.1 i₀
  map_add' x y := by simp
  map_smul' c x := by simp

noncomputable def gamma {m r : ℕ} (i₀ : Fin m) : E m r →ₗ[F] F where
  toFun x := (chart m r x).2.2.1 i₀
  map_add' x y := by simp
  map_smul' c x := by simp

lemma dotProduct_selector {k : ℕ} (c a : S k) (t : F) :
    dotProduct c (t • a) = t * dotProduct c a := by
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

def selectorFunction {k m r : ℕ}
    (e : V k m r ≃ₗ[F] S k × Data m r) (A : Fin m → S k)
    (h : S k → F) (y : V k m r) : F :=
  h (e y).1 + ∑ i : Fin m,
    dotProduct (A i) (e y).1 * (e y).2.1 i * (e y).2.2.1 i

lemma selectorFunction_embedding {k m r : ℕ}
    (e : V k m r ≃ₗ[F] S k × Data m r) (A : Fin m → S k)
    (h : S k → F) (a : S k) (x : E m r) :
    selectorFunction e A h (embedding e a x) =
      h ((chart m r x).1 • a) + (chart m r x).1 *
        ∑ i : Fin m, dotProduct (A i) a * (chart m r x).2.1 i *
          (chart m r x).2.2.1 i := by
  unfold selectorFunction
  rw [embedding_coordinates]
  simp only
  simp_rw [dotProduct_selector]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma agree_eq_chi (a b : F) : (if a = b then (1 : ℤ) else -1) = chi (a + b) := by
  rcases f2_cases a with rfl | rfl <;> rcases f2_cases b with rfl | rfl <;> rfl

lemma selectorFunction_cancel {k m r : ℕ}
    (e : V k m r ≃ₗ[F] S k × Data m r) (A : Fin m → S k)
    (h : S k → F) (a : S k) (i₀ : Fin m) (hi : dotProduct (A i₀) a ≠ 0)
    (x : E m r) :
    selectorFunction e A h (embedding e a x) +
      ((h a + h 0) * alpha m r x + h 0 +
        alpha m r x * beta i₀ x * gamma i₀ x) =
      (chart m r x).1 * ∑ i : Fin m,
        Function.update (fun i => dotProduct (A i) a) i₀ 0 i *
          (chart m r x).2.1 i * (chart m r x).2.2.1 i := by
  rw [selectorFunction_embedding]
  change h ((chart m r x).1 • a) +
      (chart m r x).1 * (∑ i, dotProduct (A i) a * (chart m r x).2.1 i *
        (chart m r x).2.2.1 i) +
      ((h a + h 0) * (chart m r x).1 + h 0 +
        (chart m r x).1 * (chart m r x).2.1 i₀ * (chart m r x).2.2.1 i₀) = _
  have hline : h ((chart m r x).1 • a) = h 0 + (h a + h 0) * (chart m r x).1 := by
    simpa using one_variable_affine (fun t : F => h (t • a)) ((chart m r x).1)
  rw [hline, cancel_active_polynomial _ _ _ i₀ hi]
  calc
    _ = (h 0 + (h a + h 0) * (chart m r x).1) +
        (h 0 + (h a + h 0) * (chart m r x).1) +
        (chart m r x).1 * ((∑ i, dotProduct (A i) a * (chart m r x).2.1 i *
          (chart m r x).2.2.1 i) + (chart m r x).2.1 i₀ * (chart m r x).2.2.1 i₀) := by ring
    _ = _ := by rw [f2_add_self, zero_add]

lemma selector_agreement_sum {k m r : ℕ}
    (e : V k m r ≃ₗ[F] S k × Data m r) (A : Fin m → S k)
    (h : S k → F) (a : S k) (i₀ : Fin m) (hi : dotProduct (A i₀) a ≠ 0) :
    (∑ x : E m r,
      if selectorFunction e A h (embedding e a x) =
        (h a + h 0) * alpha m r x + h 0 + alpha m r x * beta i₀ x * gamma i₀ x
      then (1 : ℤ) else -1) =
    ∑ t : F, ∑ u : Fin m → F, ∑ v : Fin m → F, ∑ _z : Fin r → F,
      chi (t * ∑ i : Fin m,
        Function.update (fun i => dotProduct (A i) a) i₀ 0 i * u i * v i) := by
  simp_rw [agree_eq_chi, selectorFunction_cancel e A h a i₀ hi]
  let f : Coordinates m r → ℤ := fun p =>
    chi (p.1 * ∑ i : Fin m,
      Function.update (fun i => dotProduct (A i) a) i₀ 0 i * p.2.1 i * p.2.2.1 i)
  change (∑ x : E m r, f (chart m r x)) = _
  calc
    _ = ∑ p : Coordinates m r, f p := (chart m r).toEquiv.sum_comp f
    _ = _ := by simp only [Coordinates, Data, Fintype.sum_prod_type, f]

lemma selector_agreement_scaled {k m r d : ℕ}
    (e : V k m r ≃ₗ[F] S k × Data m r) (A : Fin m → S k)
    (h : S k → F) (a : S k) (i₀ : Fin m) (hi : dotProduct (A i₀) a ≠ 0)
    (hw : ((Finset.univ : Finset (Fin m)).filter
      (fun i => dotProduct (A i) a ≠ 0)).card = d) :
    2 ^ (m + 2) * (∑ x : E m r,
      if selectorFunction e A h (embedding e a x) =
        (h a + h 0) * alpha m r x + h 0 + alpha m r x * beta i₀ x * gamma i₀ x
      then (1 : ℤ) else -1).natAbs =
      2 ^ (2 * m + r + 2) * (2 ^ m + 2 ^ (m + 1 - d)) := by
  rw [selector_agreement_sum e A h a i₀ hi]
  exact cancelled_line_exact (fun i => dotProduct (A i) a) i₀ hi hw

lemma circuit_line_attainment_of_word {k m r d : ℕ}
    (e : V k m r ≃ₗ[F] S k × Data m r) (A : Fin m → S k)
    (h : S k → F) (a : S k) (ha : a ≠ 0) (i₀ : Fin m)
    (hi : dotProduct (A i₀) a ≠ 0)
    (hw : ((Finset.univ : Finset (Fin m)).filter
      (fun i => dotProduct (A i) a ≠ 0)).card = d) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      LineCircuit.legalGates (2 * (k + 2 * m + r)) C.gates ∧
      LineCircuit.costGates C.gates = 2 * m + r + 2 ∧
      2 ^ (m + 2) *
        (∑ x : V k m r, ∑ y : V k m r,
          if C.eval (LineCircuit.bitsOf (k + 2 * m + r) x ++
            LineCircuit.bitsOf (k + 2 * m + r) y) =
            decide (dotProduct x y + selectorFunction e A h y = 1)
          then (1 : ℤ) else -1).natAbs =
        2 ^ ((k + 2 * m + r) + (2 * m + r + 2)) *
          (2 ^ m + 2 ^ (m + 1 - d)) := by
  obtain ⟨C, hleg, hcost, hraw⟩ := LineCircuit.build_projection_triple
    (embedding e a) (embedding_injective e ha)
    (alpha m r) (beta i₀) (gamma i₀) (h a + h 0) (h 0) (selectorFunction e A h)
  refine ⟨C, hleg, ?_, ?_⟩
  · exact hcost
  · rw [hraw]
    have hflat := selector_agreement_scaled e A h a i₀ hi hw
    calc
      _ = 2 ^ (k + 2 * m + r) *
          (2 ^ (m + 2) * (∑ x : E m r,
            if selectorFunction e A h (embedding e a x) =
              (h a + h 0) * alpha m r x + h 0 + alpha m r x * beta i₀ x * gamma i₀ x
            then (1 : ℤ) else -1).natAbs) := by ring
      _ = _ := by rw [hflat, pow_add]; ring

lemma circuit_line_attainment {k m r d : ℕ} (hd : 0 < d)
    (e : V k m r ≃ₗ[F] S k × Data m r) (A : Fin m → S k)
    (h : S k → F)
    (hword : ∃ a : S k, a ≠ 0 ∧
      ((Finset.univ : Finset (Fin m)).filter (fun i => dotProduct (A i) a ≠ 0)).card = d) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      LineCircuit.legalGates (2 * (k + 2 * m + r)) C.gates ∧
      LineCircuit.costGates C.gates = 2 * m + r + 2 ∧
      2 ^ (m + 2) *
        (∑ x : V k m r, ∑ y : V k m r,
          if C.eval (LineCircuit.bitsOf (k + 2 * m + r) x ++
            LineCircuit.bitsOf (k + 2 * m + r) y) =
            decide (dotProduct x y + selectorFunction e A h y = 1)
          then (1 : ℤ) else -1).natAbs =
        2 ^ ((k + 2 * m + r) + (2 * m + r + 2)) *
          (2 ^ m + 2 ^ (m + 1 - d)) := by
  classical
  obtain ⟨a, ha, hw⟩ := hword
  have hpos : 0 < ((Finset.univ : Finset (Fin m)).filter
      (fun i => dotProduct (A i) a ≠ 0)).card := by rw [hw]; exact hd
  obtain ⟨i₀, hi₀⟩ := Finset.card_pos.mp hpos
  exact circuit_line_attainment_of_word e A h a ha i₀ (Finset.mem_filter.mp hi₀).2 hw

end PEqualNP.Outside.L_meta_32057_aux.LineAttainment


namespace PEqualNP.Outside.L_meta_32057_aux

lemma binary_two_variable_interpolation
    (H : ZMod 2 → ZMod 2 → ZMod 2) (x y : ZMod 2) :
    H x y = H 0 0 + (H 1 0 - H 0 0) * x + (H 0 1 - H 0 0) * y +
      (H 1 1 - H 1 0 - H 0 1 + H 0 0) * x * y := by
  have hx : x = 0 ∨ x = 1 := by
    fin_cases x <;> first | exact Or.inl rfl | exact Or.inr rfl
  have hy : y = 0 ∨ y = 1 := by
    fin_cases y <;> first | exact Or.inl rfl | exact Or.inr rfl
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp
  ring

lemma plane_function_quadratic
    (h : (Fin 2 → ZMod 2) → ZMod 2) :
    ∃ (z : ZMod 2) (l : Fin 2 → ZMod 2) (M : Fin 2 → Fin 2 → ZMod 2),
      ∀ x, h x = z + dotProduct l x + ∑ i, ∑ j, M i j * x i * x j := by
  let z := h ![0, 0]
  let c := h ![1, 0] - z
  let d := h ![0, 1] - z
  let e := h ![1, 1] - h ![1, 0] - h ![0, 1] + z
  refine ⟨z, ![c, d], (fun i j => if i = 0 ∧ j = 1 then e else 0), ?_⟩
  intro x
  have hx : ![x 0, x 1] = x := by
    ext i
    fin_cases i <;> simp
  have hi := binary_two_variable_interpolation (fun s t => h ![s, t]) (x 0) (x 1)
  rw [hx] at hi
  simpa [z, c, d, e, dotProduct, Fin.sum_univ_two, add_assoc] using hi

lemma two_linear_forms_quadratic
    {b : ℕ} (H : ZMod 2 → ZMod 2 → ZMod 2)
    (s t : Fin b → ZMod 2) :
    ∃ (z : ZMod 2) (l : Fin b → ZMod 2) (M : Fin b → Fin b → ZMod 2),
      ∀ x, H (dotProduct s x) (dotProduct t x) =
        z + dotProduct l x + ∑ i, ∑ j, M i j * x i * x j := by
  let z := H 0 0
  let c := H 1 0 - z
  let d := H 0 1 - z
  let e := H 1 1 - H 1 0 - H 0 1 + z
  refine ⟨z, (fun i => c * s i + d * t i), (fun i j => e * s i * t j), ?_⟩
  intro x
  have hl : dotProduct (fun i => c * s i + d * t i) x =
      c * dotProduct s x + d * dotProduct t x := by
    simp [dotProduct, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  have hq : (∑ i, ∑ j, (e * s i * t j) * x i * x j) =
      e * dotProduct s x * dotProduct t x := by
    simp only [dotProduct, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hl, hq]
  simpa [z, c, d, e, add_assoc] using
    binary_two_variable_interpolation H (dotProduct s x) (dotProduct t x)

lemma affine_plane_restriction_quadratic
    {b k : ℕ} (h : (Fin k → ZMod 2) → ZMod 2)
    (a u v : Fin k → ZMod 2) (s t : Fin b → ZMod 2) :
    ∃ (z : ZMod 2) (l : Fin b → ZMod 2) (M : Fin b → Fin b → ZMod 2),
      ∀ x, h (a + dotProduct s x • u + dotProduct t x • v) =
        z + dotProduct l x + ∑ i, ∑ j, M i j * x i * x j := by
  exact two_linear_forms_quadratic (fun p q => h (a + p • u + q • v)) s t

lemma linear_form_as_dotProduct
    {b : ℕ} (p : (Fin b → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (x : Fin b → ZMod 2) :
    p x = dotProduct (fun i => p (Pi.single i 1)) x := by
  calc
    p x = p (∑ i, x i • Pi.single i 1) := congrArg p (pi_eq_sum_univ' x)
    _ = dotProduct (fun i => p (Pi.single i 1)) x := by
      simp [dotProduct, map_sum, map_smul, smul_eq_mul, mul_comm]

lemma affine_plane_linear_map_restriction_quadratic
    {b k : ℕ} (h : (Fin k → ZMod 2) → ZMod 2)
    (a u v : Fin k → ZMod 2)
    (s t : (Fin b → ZMod 2) →ₗ[ZMod 2] ZMod 2) :
    ∃ (z : ZMod 2) (l : Fin b → ZMod 2) (M : Fin b → Fin b → ZMod 2),
      ∀ x, h (a + s x • u + t x • v) =
        z + dotProduct l x + ∑ i, ∑ j, M i j * x i * x j := by
  obtain ⟨z, l, M, hq⟩ := affine_plane_restriction_quadratic h a u v
    (fun i => s (Pi.single i 1)) (fun i => t (Pi.single i 1))
  refine ⟨z, l, M, ?_⟩
  intro x
  simpa only [← linear_form_as_dotProduct s x, ← linear_form_as_dotProduct t x] using hq x


def diagonalSign (a : ZMod 2) : ℤ := if a = 0 then 1 else -1

lemma diagonalSign_add (a b : ZMod 2) :
    diagonalSign (a + b) = diagonalSign a * diagonalSign b := by
  fin_cases a <;> fin_cases b <;> rfl

lemma diagonalSign_sum {α : Type*} (s : Finset α) (f : α → ZMod 2) :
    diagonalSign (∑ i ∈ s, f i) = ∏ i ∈ s, diagonalSign (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [diagonalSign]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, diagonalSign_add, ih]

lemma diagonal_sum_factor {m : ℕ} (c : Fin m → ZMod 2) :
    (∑ u : Fin m → ZMod 2, ∑ v : Fin m → ZMod 2,
      diagonalSign (∑ j : Fin m, c j * u j * v j)) =
    ∏ j : Fin m, ∑ p : ZMod 2 × ZMod 2, diagonalSign (c j * p.1 * p.2) := by
  let F : Fin m → ZMod 2 × ZMod 2 → ℤ := fun j p => diagonalSign (c j * p.1 * p.2)
  have hps : (∏ j : Fin m, ∑ p : ZMod 2 × ZMod 2, F j p) =
      ∑ f : Fin m → ZMod 2 × ZMod 2, ∏ j : Fin m, F j (f j) := Fintype.prod_sum F
  rw [hps]
  let ePair : ((Fin m → ZMod 2) × (Fin m → ZMod 2)) ≃
      (Fin m → ZMod 2 × ZMod 2) :=
    { toFun := fun p j => (p.1 j, p.2 j)
      invFun := fun f => (fun j => (f j).1, fun j => (f j).2)
      left_inv := fun ⟨_, _⟩ => rfl
      right_inv := fun _ => rfl }
  rw [← Fintype.sum_prod_type', ← ePair.sum_comp]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [diagonalSign_sum]
  rfl

lemma diagonal_pair_sum (c : ZMod 2) :
    (∑ p : ZMod 2 × ZMod 2, diagonalSign (c * p.1 * p.2)) =
      if c = 0 then 4 else 2 := by
  fin_cases c <;> decide

lemma diagonal_filter_card_add_not {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → Prop) [DecidablePred p] :
    (s.filter p).card + (s.filter (fun x => ¬ p x)).card = s.card := by
  rw [← Finset.card_union_of_disjoint
    (Finset.disjoint_filter.mpr fun _ _ h1 h2 => h2 h1)]
  congr 1
  ext x
  simp only [Finset.mem_union, Finset.mem_filter]
  tauto

lemma diagonal_pair_product {m : ℕ} (c : Fin m → ZMod 2) :
    (∏ j : Fin m, (if c j = 0 then (4 : ℤ) else 2)) =
      2 ^ (2 * m - (Finset.univ.filter (fun i => c i ≠ 0)).card) := by
  have hc := diagonal_filter_card_add_not (Finset.univ : Finset (Fin m))
    (fun i => c i = 0)
  simp only [Finset.card_fin] at hc
  simp only [ne_eq] at *
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]
  congr 1
  omega

lemma diagonal_exact_signed_sum {m : ℕ} (c : Fin m → ZMod 2) :
    (∑ u : Fin m → ZMod 2, ∑ v : Fin m → ZMod 2,
      if (∑ i : Fin m, c i * u i * v i) = 0 then (1 : ℤ) else -1) =
      2 ^ (2 * m - (Finset.univ.filter (fun i => c i ≠ 0)).card) := by
  change (∑ u : Fin m → ZMod 2, ∑ v : Fin m → ZMod 2,
    diagonalSign (∑ i : Fin m, c i * u i * v i)) = _
  rw [diagonal_sum_factor]
  simp_rw [diagonal_pair_sum]
  exact diagonal_pair_product c

lemma diagonal_exact_signed_sum_free {m r : ℕ} (c : Fin m → ZMod 2) :
    (∑ u : Fin m → ZMod 2, ∑ v : Fin m → ZMod 2, ∑ _z : Fin r → ZMod 2,
      if (∑ i : Fin m, c i * u i * v i) = 0 then (1 : ℤ) else -1) =
      2 ^ (2 * m + r - (Finset.univ.filter (fun i => c i ≠ 0)).card) := by
  have hw : (Finset.univ.filter (fun i => c i ≠ 0)).card ≤ m := by
    simpa using Finset.card_filter_le (Finset.univ : Finset (Fin m)) (fun i => c i ≠ 0)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, ZMod.card,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  simp_rw [← Finset.mul_sum]
  rw [diagonal_exact_signed_sum, ← pow_add]
  congr 1
  omega

lemma diagonal_exact_signed_sum_free_factored {m r : ℕ} (c : Fin m → ZMod 2) :
    (∑ u : Fin m → ZMod 2, ∑ v : Fin m → ZMod 2, ∑ _z : Fin r → ZMod 2,
      if (∑ i : Fin m, c i * u i * v i) = 0 then (1 : ℤ) else -1) =
      2 ^ (m + r) * 2 ^ (m - (Finset.univ.filter (fun i => c i ≠ 0)).card) := by
  have hw : (Finset.univ.filter (fun i => c i ≠ 0)).card ≤ m := by
    simpa using Finset.card_filter_le (Finset.univ : Finset (Fin m)) (fun i => c i ≠ 0)
  rw [diagonal_exact_signed_sum_free, ← pow_add]
  congr 1
  omega

lemma diagonal_exact_flat_free {m r : ℕ} (c : Fin m → ZMod 2) :
    (∑ u : Fin m → ZMod 2, ∑ v : Fin m → ZMod 2, ∑ _z : Fin r → ZMod 2,
      if (∑ i : Fin m, c i * u i * v i) = 0 then (1 : ℤ) else -1).natAbs =
      2 ^ (2 * m + r - (Finset.univ.filter (fun i => c i ≠ 0)).card) := by
  rw [diagonal_exact_signed_sum_free]
  simp

lemma diagonal_field_sum_two (f : ZMod 2 → ℤ) :
    (∑ x : ZMod 2, f x) = f 0 + f 1 := Fin.sum_univ_two f

lemma diagonal_exact_plane_signed_sum {m r : ℕ} (c d : Fin m → ZMod 2) :
    (∑ s : ZMod 2, ∑ t : ZMod 2,
      ∑ u : Fin m → ZMod 2, ∑ v : Fin m → ZMod 2, ∑ _z : Fin r → ZMod 2,
      if (∑ i : Fin m, (s * c i + t * d i) * u i * v i) = 0
      then (1 : ℤ) else -1) =
      2 ^ (m + r) *
        (2 ^ m + 2 ^ (m - (Finset.univ.filter (fun i => c i ≠ 0)).card) +
          2 ^ (m - (Finset.univ.filter (fun i => d i ≠ 0)).card) +
          2 ^ (m - (Finset.univ.filter (fun i => c i + d i ≠ 0)).card)) := by
  simp_rw [diagonal_exact_signed_sum_free_factored, diagonal_field_sum_two]
  simp only [zero_mul, one_mul, zero_add, add_zero, ne_eq, not_true_eq_false,
    Finset.filter_false, Finset.card_empty, Nat.sub_zero]
  ring


lemma binary_module_neg
    {S : Type*} [AddCommGroup S] [Module (ZMod 2) S] (x : S) : -x = x := by
  rw [← neg_one_smul (ZMod 2) x]
  have h : (-1 : ZMod 2) = 1 := by decide
  rw [h, one_smul]

lemma plane_coefficients_injective
    {S : Type*} [AddCommGroup S] [Module (ZMod 2) S]
    (a b : S) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    Function.Injective (fun x : ZMod 2 × ZMod 2 => x.1 • a + x.2 • b) := by
  have hab0 : a + b ≠ 0 := by
    intro h
    apply hab
    exact (eq_neg_of_add_eq_zero_left h).trans (binary_module_neg b)
  have binary : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  have hz : ∀ x y : ZMod 2, x • a + y • b = 0 → x = 0 ∧ y = 0 := by
    intro x y h
    rcases binary x with rfl | rfl <;> rcases binary y with rfl | rfl
    · exact ⟨rfl, rfl⟩
    · exact False.elim (hb (by simpa only [zero_smul, one_smul, zero_add] using h))
    · exact False.elim (ha (by simpa only [zero_smul, one_smul, add_zero] using h))
    · exact False.elim (hab0 (by simpa only [one_smul] using h))
  rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ h
  have hdiff : (x₁ - y₁) • a + (x₂ - y₂) • b = 0 := by
    calc
      (x₁ - y₁) • a + (x₂ - y₂) • b =
          (x₁ • a + x₂ • b) - (y₁ • a + y₂ • b) := by simp only [sub_smul]; abel
      _ = 0 := sub_eq_zero.mpr h
  exact Prod.ext (sub_eq_zero.mp (hz _ _ hdiff).1) (sub_eq_zero.mp (hz _ _ hdiff).2)

def plane_linear_map
    {S : Type*} [AddCommGroup S] [Module (ZMod 2) S]
    (a b : S) : (ZMod 2 × ZMod 2) →ₗ[ZMod 2] S where
  toFun x := x.1 • a + x.2 • b
  map_add' x y := by simp [add_smul, add_left_comm, add_assoc]
  map_smul' c x := by simp [smul_add, mul_smul]

lemma plane_linear_map_injective
    {S : Type*} [AddCommGroup S] [Module (ZMod 2) S]
    (a b : S) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    Function.Injective (plane_linear_map a b) :=
  plane_coefficients_injective a b ha hb hab

lemma plane_product_injective
    {S W : Type*} [AddCommGroup S] [Module (ZMod 2) S]
    [AddCommGroup W] [Module (ZMod 2) W]
    (a b : S) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    Function.Injective ((plane_linear_map a b).prodMap (LinearMap.id (R := ZMod 2) (M := W))) := by
  rintro ⟨x, w⟩ ⟨y, z⟩ h
  change (plane_linear_map a b x, w) = (plane_linear_map a b y, z) at h
  apply Prod.ext
  · exact plane_linear_map_injective a b ha hb hab (congrArg (fun z : S × W => z.1) h)
  · exact congrArg (fun z : S × W => z.2) h

noncomputable def flat_model_equiv (m r : ℕ) :
    (Fin (2 * m + r + 2) → ZMod 2) ≃ₗ[ZMod 2]
      ((ZMod 2 × ZMod 2) ×
        ((Fin m → ZMod 2) × ((Fin m → ZMod 2) × (Fin r → ZMod 2)))) :=
  LinearEquiv.ofFinrankEq _ _ (by
    simp only [Module.finrank_fin_fun, Module.finrank_prod, Module.finrank_self]
    omega)

noncomputable def plane_flat_map (k m r : ℕ)
    (e : (Fin (k + 2 * m + r) → ZMod 2) ≃ₗ[ZMod 2]
      ((Fin k → ZMod 2) ×
        ((Fin m → ZMod 2) × ((Fin m → ZMod 2) × (Fin r → ZMod 2)))))
    (a b : Fin k → ZMod 2) :
    (Fin (2 * m + r + 2) → ZMod 2) →ₗ[ZMod 2] (Fin (k + 2 * m + r) → ZMod 2) :=
  e.symm.toLinearMap.comp
    (((plane_linear_map a b).prodMap LinearMap.id).comp (flat_model_equiv m r).toLinearMap)

lemma plane_flat_map_injective (k m r : ℕ)
    (e : (Fin (k + 2 * m + r) → ZMod 2) ≃ₗ[ZMod 2]
      ((Fin k → ZMod 2) ×
        ((Fin m → ZMod 2) × ((Fin m → ZMod 2) × (Fin r → ZMod 2)))))
    (a b : Fin k → ZMod 2) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    Function.Injective (plane_flat_map k m r e a b) :=
  e.symm.injective.comp
    ((plane_product_injective a b ha hb hab).comp (flat_model_equiv m r).injective)

lemma plane_flat_map_coordinates (k m r : ℕ)
    (e : (Fin (k + 2 * m + r) → ZMod 2) ≃ₗ[ZMod 2]
      ((Fin k → ZMod 2) ×
        ((Fin m → ZMod 2) × ((Fin m → ZMod 2) × (Fin r → ZMod 2)))))
    (a b : Fin k → ZMod 2) (x : Fin (2 * m + r + 2) → ZMod 2) :
    e (plane_flat_map k m r e a b x) =
      (plane_linear_map a b (flat_model_equiv m r x).1, (flat_model_equiv m r x).2) := by
  simp [plane_flat_map, LinearMap.prodMap]


lemma best_plane_exists (k m : ℕ) (hk : 2 ≤ k) (wt : (Fin k → ZMod 2) → ℕ) :
    ∃ a b : Fin k → ZMod 2, a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧
      (Finset.univ : Finset ((Fin k → ZMod 2) × (Fin k → ZMod 2))).sup
        (fun w => if w.1 ≠ 0 ∧ w.2 ≠ 0 ∧ w.1 ≠ w.2 then
          2 ^ m + 2 ^ (m - wt w.1) + 2 ^ (m - wt w.2) +
            2 ^ (m - wt (w.1 + w.2)) else 0) =
      2 ^ m + 2 ^ (m - wt a) + 2 ^ (m - wt b) + 2 ^ (m - wt (a + b)) := by
  classical
  let mass := fun w : (Fin k → ZMod 2) × (Fin k → ZMod 2) =>
    if w.1 ≠ 0 ∧ w.2 ≠ 0 ∧ w.1 ≠ w.2 then
      2 ^ m + 2 ^ (m - wt w.1) + 2 ^ (m - wt w.2) +
        2 ^ (m - wt (w.1 + w.2)) else 0
  let i : Fin k := ⟨0, by omega⟩
  let j : Fin k := ⟨1, by omega⟩
  let a : Fin k → ZMod 2 := fun x => if x.val = 0 then 1 else 0
  let b : Fin k → ZMod 2 := fun x => if x.val = 1 then 1 else 0
  have ha : a ≠ 0 := by intro h; have := congrFun h i; norm_num [a, i] at this
  have hb : b ≠ 0 := by intro h; have := congrFun h j; norm_num [b, j] at this
  have hab : a ≠ b := by intro h; have := congrFun h i; norm_num [a, b, i] at this
  obtain ⟨w, _, hw⟩ := Finset.exists_mem_eq_sup
    (Finset.univ : Finset ((Fin k → ZMod 2) × (Fin k → ZMod 2)))
    Finset.univ_nonempty mass
  have hpos : 0 < mass w := by
    have hle := Finset.le_sup (f := mass) (Finset.mem_univ (a, b))
    rw [hw] at hle
    have habmass : 0 < mass (a, b) := by
      simp only [mass, ha, hb, hab, ne_eq, not_false_eq_true, and_self, ite_true]
      positivity
    exact habmass.trans_le hle
  have hvalid : w.1 ≠ 0 ∧ w.2 ≠ 0 ∧ w.1 ≠ w.2 := by
    by_contra hn
    simp [mass, hn] at hpos
  refine ⟨w.1, w.2, hvalid.1, hvalid.2.1, hvalid.2.2, ?_⟩
  simpa only [mass, ite_eq_left hvalid] using hw

lemma plane_scale_identity (m r a b c : ℕ) (ha : a ≤ m) (hb : b ≤ m) (hc : c ≤ m) :
    2 ^ (m + 2) *
      (2 ^ (2 * m + r) + 2 ^ (2 * m + r - a) +
        2 ^ (2 * m + r - b) + 2 ^ (2 * m + r - c)) =
    2 ^ (2 * m + r + 2) *
      (2 ^ m + 2 ^ (m - a) + 2 ^ (m - b) + 2 ^ (m - c)) := by
  have hpow : ∀ w : ℕ, w ≤ m →
      2 ^ (m + 2) * 2 ^ (2 * m + r - w) =
        2 ^ (2 * m + r + 2) * 2 ^ (m - w) := by
    intro w hw
    rw [← Nat.pow_add, ← Nat.pow_add]
    congr 1
    omega
  simp only [Nat.mul_add]
  rw [hpow a ha, hpow b hb, hpow c hc]
  have hz := hpow 0 (Nat.zero_le m)
  simpa only [Nat.sub_zero] using congrArg
    (fun x => x + 2 ^ (2 * m + r + 2) * 2 ^ (m - a) +
      2 ^ (2 * m + r + 2) * 2 ^ (m - b) + 2 ^ (2 * m + r + 2) * 2 ^ (m - c)) hz


def planeCodeWeight {k m : ℕ} (A : Fin m → Fin k → ZMod 2)
    (a : Fin k → ZMod 2) : ℕ :=
  (Finset.univ.filter (fun i => dotProduct (A i) a ≠ 0)).card

def planeCodeFunction {k m r : ℕ}
    (e : (Fin (k + 2 * m + r) → ZMod 2) ≃ₗ[ZMod 2]
      ((Fin k → ZMod 2) ×
        ((Fin m → ZMod 2) × ((Fin m → ZMod 2) × (Fin r → ZMod 2)))))
    (A : Fin m → Fin k → ZMod 2) (h : (Fin k → ZMod 2) → ZMod 2)
    (y : Fin (k + 2 * m + r) → ZMod 2) : ZMod 2 :=
  h (e y).1 + ∑ i : Fin m, dotProduct (A i) (e y).1 * (e y).2.1 i * (e y).2.2.1 i

lemma plane_agreement_cancel (z p : ZMod 2) :
    (if z + p = z then (1 : ℤ) else -1) = if p = 0 then 1 else -1 := by
  fin_cases z <;> fin_cases p <;> rfl

lemma plane_pair_signed_correlation (k m r : ℕ)
    (e : (Fin (k + 2 * m + r) → ZMod 2) ≃ₗ[ZMod 2]
      ((Fin k → ZMod 2) ×
        ((Fin m → ZMod 2) × ((Fin m → ZMod 2) × (Fin r → ZMod 2)))))
    (A : Fin m → Fin k → ZMod 2) (h : (Fin k → ZMod 2) → ZMod 2)
    (a b : Fin k → ZMod 2) :
    (∑ x : Fin (2 * m + r + 2) → ZMod 2,
      if planeCodeFunction e A h (plane_flat_map k m r e a b x) =
        h (plane_linear_map a b (flat_model_equiv m r x).1) then (1 : ℤ) else -1) =
    2 ^ (m + r) *
      (2 ^ m + 2 ^ (m - planeCodeWeight A a) + 2 ^ (m - planeCodeWeight A b) +
        2 ^ (m - planeCodeWeight A (a + b))) := by
  simp only [planeCodeFunction, plane_flat_map_coordinates, plane_agreement_cancel]
  let f := fun p : (ZMod 2 × ZMod 2) ×
      ((Fin m → ZMod 2) × ((Fin m → ZMod 2) × (Fin r → ZMod 2))) =>
    if (∑ i : Fin m, dotProduct (A i) (plane_linear_map a b p.1) * p.2.1 i * p.2.2.1 i) = 0
    then (1 : ℤ) else -1
  change (∑ x, f ((flat_model_equiv m r).toEquiv x)) = _
  rw [(flat_model_equiv m r).toEquiv.sum_comp f]
  simp only [f, Fintype.sum_prod_type]
  have hcoeff : ∀ s t : ZMod 2, ∀ i : Fin m,
      dotProduct (A i) (plane_linear_map a b (s, t)) =
        s * dotProduct (A i) a + t * dotProduct (A i) b := by
    intro s t i
    simp [plane_linear_map, dotProduct_add, dotProduct_smul, smul_eq_mul]
  simp_rw [hcoeff]
  simpa only [planeCodeWeight, dotProduct_add] using
    (diagonal_exact_plane_signed_sum (r := r) (fun i => dotProduct (A i) a)
      (fun i => dotProduct (A i) b))

lemma plane_pair_attainment (k m r : ℕ)
    (e : (Fin (k + 2 * m + r) → ZMod 2) ≃ₗ[ZMod 2]
      ((Fin k → ZMod 2) ×
        ((Fin m → ZMod 2) × ((Fin m → ZMod 2) × (Fin r → ZMod 2)))))
    (A : Fin m → Fin k → ZMod 2) (h : (Fin k → ZMod 2) → ZMod 2)
    (a b : Fin k → ZMod 2) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    ∃ (L : (Fin (2 * m + r + 2) → ZMod 2) →ₗ[ZMod 2] (Fin (k + 2 * m + r) → ZMod 2))
      (q : (Fin (2 * m + r + 2) → ZMod 2) → ZMod 2),
      Function.Injective L ∧
      (∃ (z : ZMod 2) (l : Fin (2 * m + r + 2) → ZMod 2)
        (M : Fin (2 * m + r + 2) → Fin (2 * m + r + 2) → ZMod 2),
        ∀ x, q x = z + dotProduct l x + ∑ i, ∑ j, M i j * x i * x j) ∧
      2 ^ (m + 2) * (∑ x, if planeCodeFunction e A h (L x) = q x then (1 : ℤ) else -1).natAbs =
        2 ^ (2 * m + r + 2) * (2 ^ m + 2 ^ (m - planeCodeWeight A a) +
          2 ^ (m - planeCodeWeight A b) + 2 ^ (m - planeCodeWeight A (a + b))) := by
  let q := fun x => h (plane_linear_map a b (flat_model_equiv m r x).1)
  refine ⟨plane_flat_map k m r e a b, q,
    plane_flat_map_injective k m r e a b ha hb hab, ?_, ?_⟩
  · let st : (Fin (2 * m + r + 2) → ZMod 2) →ₗ[ZMod 2] (ZMod 2 × ZMod 2) :=
      (LinearMap.fst _ _ _).comp (flat_model_equiv m r).toLinearMap
    let s := (LinearMap.fst (ZMod 2) (ZMod 2) (ZMod 2)).comp st
    let t := (LinearMap.snd (ZMod 2) (ZMod 2) (ZMod 2)).comp st
    obtain ⟨z, l, M, hq⟩ := affine_plane_linear_map_restriction_quadratic h 0 a b s t
    refine ⟨z, l, M, fun x => ?_⟩
    simpa only [q, plane_linear_map, LinearMap.coe_mk, AddHom.coe_mk,
      s, t, st, LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply,
      LinearEquiv.coe_coe, zero_add] using hq x
  · have hs := plane_pair_signed_correlation k m r e A h a b
    change 2 ^ (m + 2) * (∑ x, if planeCodeFunction e A h (plane_flat_map k m r e a b x) =
      h (plane_linear_map a b (flat_model_equiv m r x).1) then (1 : ℤ) else -1).natAbs = _
    rw [hs]
    norm_cast
    rw [← Nat.mul_assoc, ← Nat.pow_add]
    congr 1
    congr 1
    omega

lemma plane_attainment (k m r : ℕ) (hk : 2 ≤ k)
    (e : (Fin (k + 2 * m + r) → ZMod 2) ≃ₗ[ZMod 2]
      ((Fin k → ZMod 2) ×
        ((Fin m → ZMod 2) × ((Fin m → ZMod 2) × (Fin r → ZMod 2)))))
    (A : Fin m → Fin k → ZMod 2) (h : (Fin k → ZMod 2) → ZMod 2) :
    ∃ (L : (Fin (2 * m + r + 2) → ZMod 2) →ₗ[ZMod 2] (Fin (k + 2 * m + r) → ZMod 2))
      (a : Fin (k + 2 * m + r) → ZMod 2)
      (q : (Fin (2 * m + r + 2) → ZMod 2) → ZMod 2),
      Function.Injective L ∧
      (∃ (z : ZMod 2) (l : Fin (2 * m + r + 2) → ZMod 2)
        (M : Fin (2 * m + r + 2) → Fin (2 * m + r + 2) → ZMod 2),
        ∀ x, q x = z + dotProduct l x + ∑ i, ∑ j, M i j * x i * x j) ∧
      2 ^ (m + 2) * (∑ x, if planeCodeFunction e A h (a + L x) = q x then (1 : ℤ) else -1).natAbs =
        2 ^ (2 * m + r + 2) *
          (Finset.univ : Finset ((Fin k → ZMod 2) × (Fin k → ZMod 2))).sup
            (fun w => if w.1 ≠ 0 ∧ w.2 ≠ 0 ∧ w.1 ≠ w.2 then
              2 ^ m + 2 ^ (m - planeCodeWeight A w.1) + 2 ^ (m - planeCodeWeight A w.2) +
                2 ^ (m - planeCodeWeight A (w.1 + w.2)) else 0) := by
  obtain ⟨a, b, ha, hb, hab, hbest⟩ := best_plane_exists k m hk (planeCodeWeight A)
  obtain ⟨L, q, hL, hq, heq⟩ := plane_pair_attainment k m r e A h a b ha hb hab
  refine ⟨L, 0, q, hL, hq, ?_⟩
  simpa only [zero_add, hbest] using heq

end PEqualNP.Outside.L_meta_32057_aux

namespace PEqualNP.Outside.L_meta_32057_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

noncomputable def circuitRaw (n : ℕ) (g : (Fin n → F2) → F2) (C : Circuit) : ℕ :=
  (∑ x : Fin n → F2, ∑ y : Fin n → F2,
    if C.eval (bitsOf n x ++ bitsOf n y) = decide (dotProduct x y + g y = 1)
    then (1 : ℤ) else -1).natAbs

lemma plane_circuit_lower (n b denom plane : ℕ) (g : (Fin n → F2) → F2)
    (B : (Fin b → F2) →ₗ[F2] (Fin n → F2))
    (a : Fin n → F2) (q : (Fin b → F2) → F2)
    (hB : Function.Injective B) (hq : isQuad q)
    (hflat : denom * (∑ x : Fin b → F2,
      if g (a + B x) = q x then (1 : ℤ) else -1).natAbs = 2 ^ b * plane) :
    ∃ C : Circuit, legalGates (2 * n) C.gates ∧ costGates C.gates ≤ b ∧
      2 ^ (n + b) * plane ≤ denom * circuitRaw n g C := by
  let f := (∑ x : Fin b → F2, if g (a + B x) = q x then (1 : ℤ) else -1).natAbs
  obtain ⟨C, hleg, hcost, hraw⟩ :=
    viaFlat_to_viaCircuit n b g (2 ^ n * f) B a q hB hq le_rfl
  refine ⟨C, hleg, hcost, ?_⟩
  calc
    2 ^ (n + b) * plane = 2 ^ n * (2 ^ b * plane) := by rw [Nat.pow_add]; ring
    _ = denom * (2 ^ n * f) := by rw [← hflat]; dsimp only [f]; ring
    _ ≤ denom * circuitRaw n g C := Nat.mul_le_mul_left _ hraw

lemma circuit_attainment_from_plane_and_line (n b denom plane line : ℕ)
    (g : (Fin n → F2) → F2)
    (hupper : ∀ C : Circuit, legalGates (2 * n) C.gates → costGates C.gates ≤ b →
      denom * circuitRaw n g C ≤ 2 ^ (n + b) * max plane line)
    (hplane : ∃ (B : (Fin b → F2) →ₗ[F2] (Fin n → F2))
        (a : Fin n → F2) (q : (Fin b → F2) → F2),
      Function.Injective B ∧ isQuad q ∧
      denom * (∑ x : Fin b → F2, if g (a + B x) = q x then (1 : ℤ) else -1).natAbs =
        2 ^ b * plane)
    (hline : ∃ C : Circuit, legalGates (2 * n) C.gates ∧ costGates C.gates ≤ b ∧
      2 ^ (n + b) * line ≤ denom * circuitRaw n g C) :
    ∃ C : Circuit, legalGates (2 * n) C.gates ∧ costGates C.gates ≤ b ∧
      denom * circuitRaw n g C = 2 ^ (n + b) * max plane line := by
  rcases le_total line plane with h | h
  · obtain ⟨B, a, q, hB, hq, hf⟩ := hplane
    obtain ⟨C, hleg, hcost, hlower⟩ := plane_circuit_lower n b denom plane g B a q hB hq hf
    refine ⟨C, hleg, hcost, le_antisymm (hupper C hleg hcost) ?_⟩
    simpa only [max_eq_left h] using hlower
  · obtain ⟨C, hleg, hcost, hlower⟩ := hline
    refine ⟨C, hleg, hcost, le_antisymm (hupper C hleg hcost) ?_⟩
    simpa only [max_eq_right h] using hlower

end PEqualNP.Outside.L_meta_32057_aux

namespace PEqualNP.Outside.L_meta_32057_aux


open scoped BigOperators

abbrev F := ZMod 2

def A1 {U : Type} [AddCommGroup U] [Module F U] (f : U → F) : Prop :=
  ∃ (c : F) (l : U →ₗ[F] F), ∀ x, f x = c + l x

def Q2 {U : Type} [AddCommGroup U] [Module F U] (q : U → F) : Prop :=
  ∃ (c : F) (l : U →ₗ[F] F) (B : U →ₗ[F] U →ₗ[F] F),
    ∀ x, q x = c + l x + B x x

def pullBilinear {U W : Type} [AddCommGroup U] [Module F U]
    [AddCommGroup W] [Module F W]
    (B : U →ₗ[F] U →ₗ[F] F) (L : W →ₗ[F] U) : W →ₗ[F] W →ₗ[F] F where
  toFun x := (B (L x)).comp L
  map_add' x y := by ext z; simp
  map_smul' c x := by ext z; simp

lemma pullBilinear_apply {U W : Type} [AddCommGroup U] [Module F U]
    [AddCommGroup W] [Module F W]
    (B : U →ₗ[F] U →ₗ[F] F) (L : W →ₗ[F] U) (x y : W) :
    pullBilinear B L x y = B (L x) (L y) := rfl

lemma a1_const {U : Type} [AddCommGroup U] [Module F U] (c : F) :
    A1 (fun _ : U => c) := ⟨c, 0, fun x => by simp⟩

lemma q2_const {U : Type} [AddCommGroup U] [Module F U] (c : F) :
    Q2 (fun _ : U => c) := ⟨c, 0, 0, fun x => by simp⟩

lemma q2_of_a1 {U : Type} [AddCommGroup U] [Module F U]
    {f : U → F} (hf : A1 f) : Q2 f := by
  obtain ⟨c, l, h⟩ := hf
  exact ⟨c, l, 0, fun x => by simpa using h x⟩

lemma a1_add {U : Type} [AddCommGroup U] [Module F U]
    {f g : U → F} (hf : A1 f) (hg : A1 g) : A1 (fun x => f x + g x) := by
  obtain ⟨c, l, h⟩ := hf
  obtain ⟨d, m, k⟩ := hg
  refine ⟨c + d, l + m, fun x => ?_⟩
  simp only [h x, k x, LinearMap.add_apply]
  ring

lemma q2_add {U : Type} [AddCommGroup U] [Module F U]
    {f g : U → F} (hf : Q2 f) (hg : Q2 g) : Q2 (fun x => f x + g x) := by
  obtain ⟨c, l, B, h⟩ := hf
  obtain ⟨d, m, C, k⟩ := hg
  refine ⟨c + d, l + m, B + C, fun x => ?_⟩
  simp only [h x, k x, LinearMap.add_apply]
  ring

lemma a1_comp_affine {U W : Type} [AddCommGroup U] [Module F U]
    [AddCommGroup W] [Module F W]
    {f : U → F} (hf : A1 f) (a : U) (L : W →ₗ[F] U) :
    A1 (fun x => f (a + L x)) := by
  obtain ⟨c, l, h⟩ := hf
  refine ⟨c + l a, l.comp L, fun x => ?_⟩
  simp [h, add_assoc]

lemma q2_comp_affine {U W : Type} [AddCommGroup U] [Module F U]
    [AddCommGroup W] [Module F W]
    {q : U → F} (hq : Q2 q) (a : U) (L : W →ₗ[F] U) :
    Q2 (fun x => q (a + L x)) := by
  obtain ⟨c, l, B, h⟩ := hq
  refine ⟨c + l a + B a a,
    l.comp L + (B a).comp L + (B.flip a).comp L,
    pullBilinear B L, fun x => ?_⟩
  simp only [h, map_add, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.flip_apply, pullBilinear_apply]
  ring

lemma q2_mul_a1 {U : Type} [AddCommGroup U] [Module F U]
    {f g : U → F} (hf : A1 f) (hg : A1 g) : Q2 (fun x => f x * g x) := by
  obtain ⟨c, l, h⟩ := hf
  obtain ⟨d, m, k⟩ := hg
  refine ⟨c * d, d • l + c • m, l.smulRight m, fun x => ?_⟩
  simp only [h x, k x, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.smulRight_apply, smul_eq_mul]
  ring

lemma a1_smul {U : Type} [AddCommGroup U] [Module F U]
    (s : F) {f : U → F} (hf : A1 f) : A1 (fun x => s * f x) := by
  obtain ⟨c, l, h⟩ := hf
  refine ⟨s * c, s • l, fun x => ?_⟩
  simp [h, mul_add]

lemma q2_smul {U : Type} [AddCommGroup U] [Module F U]
    (s : F) {q : U → F} (hq : Q2 q) : Q2 (fun x => s * q x) := by
  obtain ⟨c, l, B, h⟩ := hq
  refine ⟨s * c, s • l, s • B, fun x => ?_⟩
  simp [h, mul_add]

lemma q2_finset_sum {U α : Type} [AddCommGroup U] [Module F U]
    (s : Finset α) (f : α → U → F) (hf : ∀ a ∈ s, Q2 (f a)) :
    Q2 (fun x => ∑ a ∈ s, f a x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (q2_const (U := U) 0)
  | insert a s ha ih =>
    have h := q2_add (hf a (Finset.mem_insert_self a s))
      (ih (fun b hb => hf b (Finset.mem_insert_of_mem hb)))
    simpa only [Finset.sum_insert ha] using h

lemma q2_restrict_affine_submodule {U : Type} [AddCommGroup U] [Module F U]
    {q : U → F} (hq : Q2 q) (a : U) (K : Submodule F U) :
    Q2 (fun x : K => q (a + x.val)) := q2_comp_affine hq a K.subtype

lemma q2_derivative_a1 {U : Type} [AddCommGroup U] [Module F U]
    {q : U → F} (hq : Q2 q) (v : U) : A1 (fun x => q (x + v) + q x) := by
  obtain ⟨c, l, B, h⟩ := hq
  refine ⟨l v + B v v, B v + B.flip v, fun x => ?_⟩
  simp only [h, map_add, LinearMap.add_apply, LinearMap.flip_apply]
  have hx : (c + l x + B x x) + (c + l x + B x x) = 0 :=
    CharTwo.add_self_eq_zero _
  linear_combination hx

lemma q2_absorb_fixed_summand {U α : Type} [AddCommGroup U] [Module F U]
    [DecidableEq α] (s : Finset α) (p : α) (hp : p ∈ s)
    (c : F) (q : U → F) (a u v : α → U → F)
    (hq : Q2 q) (hu : A1 (u p)) (hv : A1 (v p)) (ha : ∀ x, a p x = c) :
    ∃ q' : U → F, Q2 q' ∧ ∀ x,
      q x + ∑ i ∈ s, a i x * u i x * v i x =
        q' x + ∑ i ∈ s.erase p, a i x * u i x * v i x := by
  refine ⟨fun x => q x + c * (u p x * v p x),
    q2_add hq (q2_smul c (q2_mul_a1 hu hv)), fun x => ?_⟩
  have hs := Finset.add_sum_erase s (fun i => a i x * u i x * v i x) hp
  rw [← hs, ha x]
  ring

lemma q2_affine_fixed_summand_elimination {U W α : Type}
    [AddCommGroup U] [Module F U] [AddCommGroup W] [Module F W]
    [DecidableEq α] (s : Finset α) (p : α) (hp : p ∈ s)
    (c : F) (q : U → F) (a u v : α → U → F) (v0 : U) (L : W →ₗ[F] U)
    (hq : Q2 q) (hu : A1 (u p)) (hv : A1 (v p))
    (ha : ∀ x, a p (v0 + L x) = c) :
    ∃ q' : W → F, Q2 q' ∧ ∀ x,
      q (v0 + L x) + ∑ i ∈ s, a i (v0 + L x) * u i (v0 + L x) * v i (v0 + L x) =
        q' x + ∑ i ∈ s.erase p,
          a i (v0 + L x) * u i (v0 + L x) * v i (v0 + L x) := by
  exact q2_absorb_fixed_summand s p hp c (fun x => q (v0 + L x))
    (fun i x => a i (v0 + L x)) (fun i x => u i (v0 + L x))
    (fun i x => v i (v0 + L x)) (q2_comp_affine hq v0 L)
    (a1_comp_affine hu v0 L) (a1_comp_affine hv v0 L) ha

lemma q2_has_bilinear_polar {U : Type} [AddCommGroup U] [Module F U]
    {q : U → F} (hq : Q2 q) :
    ∃ P : U →ₗ[F] U →ₗ[F] F,
      (∀ x y, q (x + y) + q x + q y + q 0 = P x y) ∧ (∀ x, P x x = 0) := by
  obtain ⟨c, l, B, h⟩ := hq
  refine ⟨B + B.flip, ?_, ?_⟩
  · intro x y
    simp only [h, map_add, map_zero, LinearMap.add_apply, LinearMap.flip_apply, add_zero]
    have hc : c + c = 0 := CharTwo.add_self_eq_zero _
    have hlx : l x + l x = 0 := CharTwo.add_self_eq_zero _
    have hly : l y + l y = 0 := CharTwo.add_self_eq_zero _
    have hbxx : B x x + B x x = 0 := CharTwo.add_self_eq_zero _
    have hbyy : B y y + B y y = 0 := CharTwo.add_self_eq_zero _
    linear_combination 2 * hc + hlx + hly + hbxx + hbyy
  · intro x
    simp only [LinearMap.add_apply, LinearMap.flip_apply]
    exact CharTwo.add_self_eq_zero _



lemma helper3_finrank_le_ker_add_one
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (ell : V →ₗ[K] K) :
    Module.finrank K V ≤ Module.finrank K (LinearMap.ker ell) + 1 := by
  have hr := LinearMap.finrank_range_add_finrank_ker ell
  have hle : Module.finrank K (LinearMap.range ell) ≤ 1 := by
    simpa only [Module.finrank_self] using (Submodule.finrank_le (LinearMap.range ell))
  omega

lemma helper3_kernel_preserves_surplus
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (ell : V →ₗ[K] K) (B : ℕ)
    (hB : B + 2 ≤ Module.finrank K V) :
    B + 1 ≤ Module.finrank K (LinearMap.ker ell) := by
  have h := helper3_finrank_le_ker_add_one ell
  omega

lemma helper3_nonzero_kernel_finrank
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (ell : V →ₗ[K] K) (v : V) (hv : ell v = 1) :
    Module.finrank K (LinearMap.ker ell) + 1 = Module.finrank K V := by
  have hr := LinearMap.finrank_range_add_finrank_ker ell
  have hsurj : Function.Surjective ell := by
    intro c
    exact ⟨c • v, by simp [hv]⟩
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self] at hr
  omega

lemma helper3_coordinate_deletion_surplus
    {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V]
    (ell : V →ₗ[K] K) (del : LinearMap.ker ell →ₗ[K] W)
    (hdel : Function.Injective del) (B : ℕ)
    (hB : B + 2 ≤ Module.finrank K V) (hpos : 1 ≤ B) :
    (B - 1) + 2 ≤ Module.finrank K (LinearMap.range del) := by
  have hk := helper3_kernel_preserves_surplus ell B hB
  have he := (LinearEquiv.ofInjective del hdel).finrank_eq
  omega

noncomputable def helper3_deleteData
    {K S ι : Type*} [Field K] [AddCommGroup S] [Module K S] (p : ι) :
    (S × (ι → K)) →ₗ[K] (S × ({i : ι // i ≠ p} → K)) where
  toFun := fun x => (x.1, fun i => x.2 i.1)
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

lemma helper3_deleteData_injective_on_submodule
    {K S ι : Type*} [Field K] [AddCommGroup S] [Module K S] [DecidableEq ι]
    (W : Submodule K (S × (ι → K))) (p : ι)
    (hp : (0, Pi.single p (1 : K)) ∉ W) :
    Function.Injective ((helper3_deleteData (K := K) (S := S) p).comp W.subtype) := by
  intro x y hxy
  let z : S × (ι → K) := (x : S × (ι → K)) - (y : S × (ι → K))
  have hzW : z ∈ W := W.sub_mem x.property y.property
  have hfirst : z.1 = 0 := by
    have h := congrArg Prod.fst hxy
    change x.val.1 = y.val.1 at h
    exact sub_eq_zero.mpr h
  have hzOther (i : ι) (hi : i ≠ p) : z.2 i = 0 := by
    have h := congrFun (congrArg Prod.snd hxy) ⟨i, hi⟩
    exact sub_eq_zero.mpr h
  have hzp : z.2 p = 0 := by
    by_contra hn
    have haxis : (z.2 p)⁻¹ • z = (0, Pi.single p (1 : K)) := by
      apply Prod.ext
      · change (z.2 p)⁻¹ • z.1 = 0
        simp [hfirst]
      · funext i
        by_cases hi : i = p
        · subst i
          simp [Pi.smul_apply, smul_eq_mul, hn]
        · simp [Pi.smul_apply, smul_eq_mul, hzOther i hi, hi]
    apply hp
    rw [← haxis]
    exact W.smul_mem _ hzW
  apply Subtype.ext
  apply sub_eq_zero.mp
  change z = 0
  apply Prod.ext hfirst
  funext i
  by_cases hi : i = p
  · simpa [hi] using hzp
  · exact hzOther i hi

lemma helper3_deleteData_comp_injective
    {K U S ι : Type*} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup S] [Module K S] [DecidableEq ι]
    (L : U →ₗ[K] (S × (ι → K))) (hL : Function.Injective L) (p : ι)
    (hp : (0, Pi.single p (1 : K)) ∉ LinearMap.range L) :
    Function.Injective ((helper3_deleteData (K := K) (S := S) p).comp L) := by
  intro x y hxy
  apply hL
  have h := helper3_deleteData_injective_on_submodule (LinearMap.range L) p hp
    (a₁ := ⟨L x, ⟨x, rfl⟩⟩) (a₂ := ⟨L y, ⟨y, rfl⟩⟩) hxy
  exact congrArg Subtype.val h

lemma helper3_split_deleteData_injective
    {K U S ι : Type*} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup S] [Module K S] [DecidableEq ι]
    (L : U →ₗ[K] (S × (ι → K))) (hL : Function.Injective L) (p : ι)
    (hp : (0, Pi.single p (1 : K)) ∉ LinearMap.range L) (ell : U →ₗ[K] K) :
    Function.Injective (((helper3_deleteData (K := K) (S := S) p).comp L).comp
      (LinearMap.ker ell).subtype) := by
  exact (helper3_deleteData_comp_injective L hL p hp).comp Subtype.val_injective

lemma helper3_split_row_vanishes
    {K U S ι : Type*} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup S] [Module K S]
    (L : U →ₗ[K] (S × (ι → K))) (row : S →ₗ[K] K)
    (u : LinearMap.ker (row.comp ((LinearMap.fst K S (ι → K)).comp L))) :
    row (L u.val).1 = 0 := u.property

lemma helper3_split_row_constant
    {K U S ι : Type*} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup S] [Module K S]
    (L : U →ₗ[K] (S × (ι → K))) (row : S →ₗ[K] K)
    (a : S × (ι → K)) (u0 : U) (hu0 : row (L u0).1 = 1) (c : K)
    (u : LinearMap.ker (row.comp ((LinearMap.fst K S (ι → K)).comp L))) :
    row (a + L (c • u0 + u.val)).1 = row a.1 + c := by
  have hu : row (L u.val).1 = 0 := u.property
  simp [map_add, map_smul, hu0, hu, smul_eq_mul]

noncomputable def helper3_splitEquiv
    {K U : Type*} [Field K] [AddCommGroup U] [Module K U]
    (ell : U →ₗ[K] K) (u0 : U) (hu0 : ell u0 = 1) :
    (K × LinearMap.ker ell) ≃ U where
  toFun := fun v => v.2.val + v.1 • u0
  invFun := fun x => (ell x, ⟨x - ell x • u0, by simp [hu0]⟩)
  left_inv := by
    rintro ⟨c, v⟩
    apply Prod.ext
    · simp [hu0]
    · apply Subtype.ext
      simp [hu0]
  right_inv := fun x => sub_add_cancel x (ell x • u0)

lemma helper3_exact_split_sum
    {K U : Type*} [Field K] [Fintype K] [AddCommGroup U] [Module K U] [Fintype U]
    (ell : U →ₗ[K] K) [Fintype (LinearMap.ker ell)]
    (u0 : U) (hu0 : ell u0 = 1) (f : U → ℤ) :
    (∑ x : U, f x) = ∑ c : K, ∑ v : LinearMap.ker ell, f (c • u0 + v.val) := by
  classical
  let e := helper3_splitEquiv ell u0 hu0
  rw [← Fintype.sum_equiv e _ _ (fun _ => rfl), Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro v _
  simp only [e, helper3_splitEquiv, Equiv.coe_fn_mk, add_comm]

lemma helper3_exact_split_delete_sum
    {K U W : Type*} [Field K] [Fintype K] [AddCommGroup U] [Module K U] [Fintype U]
    [AddCommGroup W] [Module K W]
    (ell : U →ₗ[K] K) [Fintype (LinearMap.ker ell)]
    (u0 : U) (hu0 : ell u0 = 1)
    (del : LinearMap.ker ell →ₗ[K] W) (hdel : Function.Injective del)
    [Fintype (LinearMap.range del)] (f : U → ℤ) :
    (∑ x : U, f x) = ∑ c : K, ∑ v : LinearMap.range del,
      f (c • u0 + ((LinearEquiv.ofInjective del hdel).symm v).val) := by
  rw [helper3_exact_split_sum ell u0 hu0 f]
  apply Finset.sum_congr rfl
  intro c _
  refine Fintype.sum_equiv (LinearEquiv.ofInjective del hdel).toEquiv _ _ ?_
  intro v
  simp

lemma helper3_exact_affine_split_sum
    {K U V : Type*} [Field K] [Fintype K] [AddCommGroup U] [Module K U] [Fintype U]
    [AddCommGroup V] [Module K V]
    (ell : U →ₗ[K] K) [Fintype (LinearMap.ker ell)]
    (u0 : U) (hu0 : ell u0 = 1) (L : U →ₗ[K] V) (a : V) (f : V → ℤ) :
    (∑ x : U, f (a + L x)) =
      ∑ c : K, ∑ v : LinearMap.ker ell, f ((a + L (c • u0)) + L v.val) := by
  rw [helper3_exact_split_sum ell u0 hu0 (fun x => f (a + L x))]
  simp only [map_add, add_assoc]
lemma helper3_split_delete_step
    {K U S J : Type*} [Field K] [AddCommGroup U] [Module K U]
    [FiniteDimensional K U] [AddCommGroup S] [Module K S] [Fintype J] [DecidableEq J]
    (L : U →ₗ[K] (S × (J → K))) (hL : Function.Injective L) (p : J)
    (hp : (0, Pi.single p (1 : K)) ∉ LinearMap.range L)
    (ell : U →ₗ[K] K) (d : ℕ) (hsur : Fintype.card J + d ≤ Module.finrank K U) :
    let L' := ((helper3_deleteData (K := K) (S := S) p).comp L).comp
      (LinearMap.ker ell).subtype
    Function.Injective L' ∧
      Fintype.card {j : J // j ≠ p} + d ≤ Module.finrank K (LinearMap.ker ell) ∧
      ∀ u : LinearMap.ker ell, (L' u).1 = (L u.val).1 := by
  classical
  refine ⟨helper3_split_deleteData_injective L hL p hp ell, ?_, fun _ => rfl⟩
  have hcard := Fintype.card_congr (Equiv.optionSubtypeNe p)
  simp only [Fintype.card_option] at hcard
  have hker := helper3_finrank_le_ker_add_one ell
  omega

lemma helper3_delete_step
    {K U S J : Type*} [Field K] [AddCommGroup U] [Module K U]
    [FiniteDimensional K U] [AddCommGroup S] [Module K S] [Fintype J] [DecidableEq J]
    (L : U →ₗ[K] (S × (J → K))) (hL : Function.Injective L) (p : J)
    (hp : (0, Pi.single p (1 : K)) ∉ LinearMap.range L)
    (d : ℕ) (hsur : Fintype.card J + d ≤ Module.finrank K U) :
    let L' := (helper3_deleteData (K := K) (S := S) p).comp L
    Function.Injective L' ∧
      Fintype.card {j : J // j ≠ p} + (d + 1) ≤ Module.finrank K U ∧
      ∀ u : U, (L' u).1 = (L u).1 := by
  classical
  refine ⟨helper3_deleteData_comp_injective L hL p hp, ?_, fun _ => rfl⟩
  have hcard := Fintype.card_congr (Equiv.optionSubtypeNe p)
  simp only [Fintype.card_option] at hcard
  omega

lemma helper3_zero_or_normalized_vector
    {K U : Type*} [Field K] [AddCommGroup U] [Module K U]
    (ell : U →ₗ[K] K) : ell = 0 ∨ ∃ u0 : U, ell u0 = 1 := by
  classical
  by_cases hzero : ell = 0
  · exact Or.inl hzero
  · apply Or.inr
    have hex : ∃ v : U, ell v ≠ 0 := by
      by_contra hn
      push Not at hn
      apply hzero
      ext v
      exact hn v
    obtain ⟨v, hv⟩ := hex
    exact ⟨(ell v)⁻¹ • v, by simp [hv]⟩

lemma helper3_natAbs_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    (∑ i ∈ s, f i).natAbs ≤ ∑ i ∈ s, (f i).natAbs := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (Int.natAbs_add_le _ _).trans (Nat.add_le_add_left ih _)

lemma helper3_split_bound_aggregation
    {K U : Type*} [Field K] [Fintype K] [AddCommGroup U] [Module K U] [Fintype U]
    (ell : U →ₗ[K] K) [Fintype (LinearMap.ker ell)]
    (u0 : U) (hu0 : ell u0 = 1) (f : U → ℤ) (D R : ℕ)
    (hbranch : ∀ c : K,
      D * (∑ v : LinearMap.ker ell, f (c • u0 + v.val)).natAbs ≤
        R * Fintype.card (LinearMap.ker ell)) :
    D * (∑ u : U, f u).natAbs ≤ R * Fintype.card U := by
  classical
  have hcard : Fintype.card K * Fintype.card (LinearMap.ker ell) = Fintype.card U := by
    simpa only [Fintype.card_prod] using Fintype.card_congr (helper3_splitEquiv ell u0 hu0)
  rw [helper3_exact_split_sum ell u0 hu0 f]
  calc
    D * (∑ c : K, ∑ v : LinearMap.ker ell, f (c • u0 + v.val)).natAbs
        ≤ D * ∑ c : K, (∑ v : LinearMap.ker ell, f (c • u0 + v.val)).natAbs :=
      Nat.mul_le_mul_left D (helper3_natAbs_sum_le Finset.univ _)
    _ = ∑ c : K, D * (∑ v : LinearMap.ker ell, f (c • u0 + v.val)).natAbs :=
      Finset.mul_sum _ _ _
    _ ≤ ∑ _c : K, R * Fintype.card (LinearMap.ker ell) :=
      Finset.sum_le_sum (fun c _ => hbranch c)
    _ = R * Fintype.card U := by
      simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
      rw [← hcard]
      exact Nat.mul_left_comm _ _ _

lemma helper3_exact_binary_split_sum
    {U : Type*} [AddCommGroup U] [Module (ZMod 2) U] [Fintype U]
    (ell : U →ₗ[ZMod 2] ZMod 2) [Fintype (LinearMap.ker ell)]
    (u0 : U) (hu0 : ell u0 = 1) (f : U → ℤ) :
    (∑ u : U, f u) = (∑ v : LinearMap.ker ell, f v.val) +
      ∑ v : LinearMap.ker ell, f (u0 + v.val) := by
  classical
  rw [helper3_exact_split_sum (K := ZMod 2) (U := U) ell u0 hu0 f]
  have huniv : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  rw [huniv]
  simp


def deleteFreeEmbedding {I J : Type*} (pos : I × Bool ↪ J) (p : J)
    (hp : ∀ i, pos i ≠ p) : I × Bool ↪ {j : J // j ≠ p} where
  toFun i := ⟨pos i, hp i⟩
  inj' _ _ h := pos.injective (congrArg Subtype.val h)

def deletePairEmbedding {I J : Type*} (pos : I × Bool ↪ J) (i : I) (b : Bool) :
    {i' : I // i' ≠ i} × Bool ↪ {j : J // j ≠ pos (i, b)} where
  toFun j := ⟨pos (j.1.val, j.2), by
    intro h
    exact j.1.property (congrArg Prod.fst (pos.injective h))⟩
  inj' j k h := by
    have he := pos.injective (congrArg Subtype.val h)
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst he)
    · exact congrArg (fun z : I × Bool => z.2) he

lemma card_delete_coordinate {J : Type*} [Fintype J] [DecidableEq J] (p : J) :
    Fintype.card {j : J // j ≠ p} + 1 = Fintype.card J := by
  simpa only [Fintype.card_option] using Fintype.card_congr (Equiv.optionSubtypeNe p)

lemma delete_pair_product {I J K : Type*} [Mul K]
    (pos : I × Bool ↪ J) (i : I) (b : Bool) (x : J → K)
    (j : {i' : I // i' ≠ i}) :
    (fun p : {p : J // p ≠ pos (i, b)} => x p.val)
        (deletePairEmbedding pos i b (j, false)) *
      (fun p : {p : J // p ≠ pos (i, b)} => x p.val)
        (deletePairEmbedding pos i b (j, true)) =
      x (pos (j.val, false)) * x (pos (j.val, true)) := rfl


open scoped BigOperators


lemma vertical_vectors_of_axes {K S J : Type*} [Field K]
    [AddCommGroup S] [Module K S] [Fintype J] [DecidableEq J]
    (W : Submodule K (S × (J → K)))
    (haxes : ∀ j : J, (0, Pi.single j (1 : K)) ∈ W) :
    ∀ v : J → K, (0, v) ∈ W := by
  intro v
  have hs : (∑ j : J, v j • ((0 : S), Pi.single j (1 : K))) = (0, v) := by
    apply Prod.ext
    · change (LinearMap.fst K S (J → K)) (∑ j : J, v j • ((0 : S), Pi.single j (1 : K))) = 0
      rw [map_sum]
      simp
    · funext j
      change ((LinearMap.snd K S (J → K)) (∑ i : J, v i • ((0 : S), Pi.single i (1 : K)))) j = v j
      rw [map_sum]
      simp [Pi.single_apply, Finset.sum_apply, smul_eq_mul]
  rw [← hs]
  exact W.sum_mem (fun j _ => W.smul_mem (v j) (haxes j))

lemma missing_data_axis_or_vertical {K S J : Type*} [Field K]
    [AddCommGroup S] [Module K S] [Fintype J] [DecidableEq J]
    (W : Submodule K (S × (J → K))) :
    (∃ j : J, (0, Pi.single j (1 : K)) ∉ W) ∨
      ∀ v : J → K, (0, v) ∈ W := by
  classical
  by_cases h : ∀ j : J, (0, Pi.single j (1 : K)) ∈ W
  · exact Or.inr (vertical_vectors_of_axes W h)
  · exact Or.inl (not_forall.mp h)


open scoped BigOperators

lemma basisfree_sum_delete {I : Type} [Fintype I] [DecidableEq I]
    (i : I) (f : I → F) :
    ∑ j, f j = f i + ∑ j : {j : I // j ≠ i}, f j.val := by
  rw [← Finset.sum_add_sum_compl ({i} : Finset I) f, Finset.sum_singleton]
  congr 1
  symm
  refine Finset.sum_bij (fun (j : {j : I // j ≠ i}) _ => j.val) ?_ ?_ ?_ ?_
  · intro j _; simp [j.property]
  · intro j k _ _ h; exact Subtype.ext h
  · intro j hj
    simp only [Finset.mem_compl, Finset.mem_singleton] at hj
    exact ⟨⟨j, hj⟩, Finset.mem_univ _, rfl⟩
  · intro _ _; rfl

lemma a1_data_coordinate {U S J : Type}
    [AddCommGroup U] [Module F U] [AddCommGroup S] [Module F S]
    (a : S × (J → F)) (L : U →ₗ[F] (S × (J → F))) (j : J) :
    A1 (fun x => (a + L x).2 j) := by
  refine ⟨a.2 j, (LinearMap.proj j).comp ((LinearMap.snd F S (J → F)).comp L), ?_⟩
  intro x
  rfl

lemma pair_elimination_step
    {U S I J : Type} [AddCommGroup U] [Module F U]
    [AddCommGroup S] [Module F S] [Fintype I] [DecidableEq I]
    (pos : I × Bool ↪ J) (A : I → S →ₗ[F] F) (h : S → F)
    (a : S × (J → F)) (L : U →ₗ[F] (S × (J → F)))
    (q : U → F) (hq : Q2 q) (i : I) (b : Bool) (w : U) :
    let ell := (A i).comp ((LinearMap.fst F S (J → F)).comp L)
    let K := LinearMap.ker ell
    let del := helper3_deleteData (K := F) (S := S) (pos (i, b))
    let a' := del (a + L w)
    let L' := (del.comp L).comp K.subtype
    ∃ q' : K → F, Q2 q' ∧ ∀ x : K,
      q (w + x.val) + h (a + L (w + x.val)).1 +
          ∑ j, A j (a + L (w + x.val)).1 *
            (a + L (w + x.val)).2 (pos (j, false)) *
            (a + L (w + x.val)).2 (pos (j, true)) =
        q' x + h (a' + L' x).1 +
          ∑ j : {j : I // j ≠ i}, A j.val (a' + L' x).1 *
            (a' + L' x).2 (deletePairEmbedding pos i b (j, false)) *
            (a' + L' x).2 (deletePairEmbedding pos i b (j, true)) := by
  dsimp only
  let ell := (A i).comp ((LinearMap.fst F S (J → F)).comp L)
  let K := LinearMap.ker ell
  let c := A i (a + L w).1
  let u : K → F := fun x => (a + L (w + x.val)).2 (pos (i, false))
  let v : K → F := fun x => (a + L (w + x.val)).2 (pos (i, true))
  have hu : A1 u :=
    a1_comp_affine (a1_data_coordinate a L (pos (i, false))) w K.subtype
  have hv : A1 v :=
    a1_comp_affine (a1_data_coordinate a L (pos (i, true))) w K.subtype
  refine ⟨fun x => q (w + x.val) + c * u x * v x,
    q2_add (q2_comp_affine hq w K.subtype) (q2_mul_a1 (a1_smul c hu) hv), ?_⟩
  intro x
  have hc : A i (a + L (w + x.val)).1 = c := by
    have hx : A i (L x.val).1 = 0 := x.property
    simp [c, map_add, hx]
  have hy : a + L (w + x.val) = a + L w + L x.val := by
    rw [map_add, add_assoc]
  have hyu : u x = (a + L w + L x.val).2 (pos (i, false)) := by
    dsimp only [u]
    rw [hy]
  have hyv : v x = (a + L w + L x.val).2 (pos (i, true)) := by
    dsimp only [v]
    rw [hy]
  rw [hy] at hc ⊢
  rw [basisfree_sum_delete i, hc]
  change q (w + x.val) + h (a + L w + L x.val).1 +
      (c * (a + L w + L x.val).2 (pos (i, false)) *
        (a + L w + L x.val).2 (pos (i, true)) +
        ∑ j : {j : I // j ≠ i}, A j.val (a + L w + L x.val).1 *
          (a + L w + L x.val).2 (pos (j.val, false)) *
          (a + L w + L x.val).2 (pos (j.val, true))) =
      (q (w + x.val) + c * u x * v x) + h (a + L w + L x.val).1 +
        ∑ j : {j : I // j ≠ i}, A j.val (a + L w + L x.val).1 *
          (a + L w + L x.val).2 (pos (j.val, false)) *
          (a + L w + L x.val).2 (pos (j.val, true))
  rw [hyu, hyv]
  ring


open scoped BigOperators

lemma pair_elimination_along_linear
    {U W S I J : Type} [AddCommGroup U] [Module F U]
    [AddCommGroup W] [Module F W]
    [AddCommGroup S] [Module F S] [Fintype I] [DecidableEq I]
    (pos : I × Bool ↪ J) (A : I → S →ₗ[F] F) (h : S → F)
    (a : S × (J → F)) (L : U →ₗ[F] (S × (J → F)))
    (q : U → F) (hq : Q2 q) (i : I) (b : Bool) (w : U)
    (B : W →ₗ[F] U) (hB : ∀ x, A i (L (B x)).1 = 0) :
    let del := helper3_deleteData (K := F) (S := S) (pos (i, b))
    let a' := del (a + L w)
    let L' := (del.comp L).comp B
    ∃ q' : W → F, Q2 q' ∧ ∀ x : W,
      q (w + (B x)) + h (a + L (w + (B x))).1 +
          ∑ j, A j (a + L (w + (B x))).1 *
            (a + L (w + (B x))).2 (pos (j, false)) *
            (a + L (w + (B x))).2 (pos (j, true)) =
        q' x + h (a' + L' x).1 +
          ∑ j : {j : I // j ≠ i}, A j.val (a' + L' x).1 *
            (a' + L' x).2 (deletePairEmbedding pos i b (j, false)) *
            (a' + L' x).2 (deletePairEmbedding pos i b (j, true)) := by
  dsimp only
  let c := A i (a + L w).1
  let u : W → F := fun x => (a + L (w + (B x))).2 (pos (i, false))
  let v : W → F := fun x => (a + L (w + (B x))).2 (pos (i, true))
  have hu : A1 u :=
    a1_comp_affine (a1_data_coordinate a L (pos (i, false))) w B
  have hv : A1 v :=
    a1_comp_affine (a1_data_coordinate a L (pos (i, true))) w B
  refine ⟨fun x => q (w + (B x)) + c * u x * v x,
    q2_add (q2_comp_affine hq w B) (q2_mul_a1 (a1_smul c hu) hv), ?_⟩
  intro x
  have hc : A i (a + L (w + (B x))).1 = c := by
    have hx : A i (L (B x)).1 = 0 := hB x
    simp [c, map_add, hx]
  have hy : a + L (w + (B x)) = a + L w + L (B x) := by
    rw [map_add, add_assoc]
  have hyu : u x = (a + L w + L (B x)).2 (pos (i, false)) := by
    dsimp only [u]
    rw [hy]
  have hyv : v x = (a + L w + L (B x)).2 (pos (i, true)) := by
    dsimp only [v]
    rw [hy]
  rw [hy] at hc ⊢
  rw [basisfree_sum_delete i, hc]
  change q (w + (B x)) + h (a + L w + L (B x)).1 +
      (c * (a + L w + L (B x)).2 (pos (i, false)) *
        (a + L w + L (B x)).2 (pos (i, true)) +
        ∑ j : {j : I // j ≠ i}, A j.val (a + L w + L (B x)).1 *
          (a + L w + L (B x)).2 (pos (j.val, false)) *
          (a + L w + L (B x)).2 (pos (j.val, true))) =
      (q (w + (B x)) + c * u x * v x) + h (a + L w + L (B x)).1 +
        ∑ j : {j : I // j ≠ i}, A j.val (a + L w + L (B x)).1 *
          (a + L w + L (B x)).2 (pos (j.val, false)) *
          (a + L w + L (B x)).2 (pos (j.val, true))
  rw [hyu, hyv]
  ring


lemma free_coordinate_elimination_along_linear
    {U W S I J : Type} [AddCommGroup U] [Module F U]
    [AddCommGroup W] [Module F W] [AddCommGroup S] [Module F S]
    [Fintype I]
    (pos : I × Bool ↪ J) (A : I → S →ₗ[F] F) (h : S → F)
    (a : S × (J → F)) (L : U →ₗ[F] (S × (J → F)))
    (q : U → F) (hq : Q2 q) (p : J) (hp : ∀ i, pos i ≠ p)
    (w : U) (B : W →ₗ[F] U) :
    let del := helper3_deleteData (K := F) (S := S) p
    let a' := del (a + L w)
    let L' := (del.comp L).comp B
    ∃ q' : W → F, Q2 q' ∧ ∀ x : W,
      q (w + B x) + h (a + L (w + B x)).1 +
          ∑ j, A j (a + L (w + B x)).1 *
            (a + L (w + B x)).2 (pos (j, false)) *
            (a + L (w + B x)).2 (pos (j, true)) =
        q' x + h (a' + L' x).1 +
          ∑ j, A j (a' + L' x).1 *
            (a' + L' x).2 (deleteFreeEmbedding pos p hp (j, false)) *
            (a' + L' x).2 (deleteFreeEmbedding pos p hp (j, true)) := by
  dsimp only
  refine ⟨fun x => q (w + B x), q2_comp_affine hq w B, fun x => ?_⟩
  have hy : a + L (w + B x) = a + L w + L (B x) := by
    rw [map_add, add_assoc]
  rw [hy]
  rfl

noncomputable def helper3_codeWeight
    {F S I : Type*} [Field F] [AddCommGroup S] [Module F S] [Fintype I] [DecidableEq I]
    (A : I → S →ₗ[F] F) (a : S) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => A i a ≠ 0)).card

noncomputable def helper3_planeCap
    {F S I : Type*} [Field F] [AddCommGroup S] [Module F S] [Fintype I] [DecidableEq I]
    (A : I → S →ₗ[F] F) (T : Submodule F S) (D R : ℕ) : Prop :=
    ∀ a b : S, a ∈ T → b ∈ T → a ≠ 0 → b ≠ 0 → a ≠ b →
      (D : ℚ) * (1 + (1 / 2 : ℚ) ^ helper3_codeWeight A a +
        (1 / 2 : ℚ) ^ helper3_codeWeight A b +
        (1 / 2 : ℚ) ^ helper3_codeWeight A (a + b)) ≤ 4 * (R : ℚ)

lemma helper3_planeCap_mono
    {F S I : Type*} [Field F] [AddCommGroup S] [Module F S] [Fintype I] [DecidableEq I]
    (A : I → S →ₗ[F] F) {T T' : Submodule F S} {D R : ℕ}
    (hcap : helper3_planeCap A T D R) (hT : T' ≤ T) :
    helper3_planeCap A T' D R := by
  intro a b ha hb hna hnb hab
  exact hcap a b (hT ha) (hT hb) hna hnb hab

lemma helper3_codeWeight_erase_eq
    {F S I : Type*} [Field F] [AddCommGroup S] [Module F S] [Fintype I] [DecidableEq I]
    (A : I → S →ₗ[F] F) (p : I) (a : S) (hp : A p a = 0) :
    helper3_codeWeight (fun i : {i : I // i ≠ p} => A i.val) a =
      helper3_codeWeight A a := by
  classical
  unfold helper3_codeWeight
  refine Finset.card_bij (fun (i : {i : I // i ≠ p}) _ => i.val) ?_ ?_ ?_
  · intro i hi
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hi
  · intro i hi j hj hij
    exact Subtype.ext hij
  · intro i hi
    have hia : A i a ≠ 0 := (Finset.mem_filter.mp hi).2
    have hip : i ≠ p := by
      intro he
      subst i
      exact hia hp
    exact ⟨⟨i, hip⟩, by simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hia, rfl⟩

lemma helper3_planeCap_erase_iff
    {F S I : Type*} [Field F] [AddCommGroup S] [Module F S] [Fintype I] [DecidableEq I]
    (A : I → S →ₗ[F] F) (p : I) (T : Submodule F S) (D R : ℕ)
    (hp : ∀ a ∈ T, A p a = 0) :
    helper3_planeCap (fun i : {i : I // i ≠ p} => A i.val) T D R ↔
      helper3_planeCap A T D R := by
  constructor <;> intro h a b ha hb hna hnb hab
  · have hh := h a b ha hb hna hnb hab
    rw [helper3_codeWeight_erase_eq A p a (hp a ha),
      helper3_codeWeight_erase_eq A p b (hp b hb),
      helper3_codeWeight_erase_eq A p (a + b) (hp _ (T.add_mem ha hb))] at hh
    exact hh
  · rw [helper3_codeWeight_erase_eq A p a (hp a ha),
      helper3_codeWeight_erase_eq A p b (hp b hb),
      helper3_codeWeight_erase_eq A p (a + b) (hp _ (T.add_mem ha hb))]
    exact h a b ha hb hna hnb hab

lemma helper3_planeCap_erase_mono
    {F S I : Type*} [Field F] [AddCommGroup S] [Module F S] [Fintype I] [DecidableEq I]
    (A : I → S →ₗ[F] F) (p : I) {T T' : Submodule F S} {D R : ℕ}
    (hcap : helper3_planeCap A T D R) (hT : T' ≤ T)
    (hp : ∀ a ∈ T', A p a = 0) :
    helper3_planeCap (fun i : {i : I // i ≠ p} => A i.val) T' D R := by
  apply (helper3_planeCap_erase_iff A p T' D R hp).mpr
  exact helper3_planeCap_mono A hcap hT

lemma helper3_planeCap_split_erase
    {F U S I : Type*} [Field F] [AddCommGroup U] [Module F U]
    [AddCommGroup S] [Module F S] [Fintype I] [DecidableEq I]
    (A : I → S →ₗ[F] F) (p : I) (B : U →ₗ[F] S) {D R : ℕ}
    (hcap : helper3_planeCap A (LinearMap.range B) D R) :
    helper3_planeCap (fun i : {i : I // i ≠ p} => A i.val)
      (LinearMap.range (B.comp (LinearMap.ker ((A p).comp B)).subtype)) D R := by
  apply helper3_planeCap_erase_mono A p hcap
  · rintro a ⟨u, rfl⟩
    exact ⟨u.val, rfl⟩
  · rintro a ⟨u, rfl⟩
    exact u.property

lemma helper3_planeCap_split_delete
    {F U S I J : Type*} [Field F] [AddCommGroup U] [Module F U]
    [AddCommGroup S] [Module F S] [Fintype I] [DecidableEq I]
    (A : I → S →ₗ[F] F) (i : I) (p : J) (L : U →ₗ[F] (S × (J → F))) {D R : ℕ}
    (hcap : helper3_planeCap A
      (LinearMap.range ((LinearMap.fst F S (J → F)).comp L)) D R) :
    let B := (LinearMap.fst F S (J → F)).comp L
    let L' := ((helper3_deleteData (K := F) p).comp L).comp
      (LinearMap.ker ((A i).comp B)).subtype
    helper3_planeCap (fun j : {j : I // j ≠ i} => A j.val)
      (LinearMap.range ((LinearMap.fst F S ({j : J // j ≠ p} → F)).comp L')) D R := by
  dsimp only
  exact helper3_planeCap_split_erase A i
    ((LinearMap.fst F S (J → F)).comp L) hcap

lemma helper3_planeCap_erase_zero_comp
    {F U S I : Type*} [Field F] [AddCommGroup U] [Module F U]
    [AddCommGroup S] [Module F S] [Fintype I] [DecidableEq I]
    (A : I → S →ₗ[F] F) (p : I) (B : U →ₗ[F] S) {D R : ℕ}
    (hcap : helper3_planeCap A (LinearMap.range B) D R)
    (hzero : (A p).comp B = 0) :
    helper3_planeCap (fun i : {i : I // i ≠ p} => A i.val) (LinearMap.range B) D R := by
  apply (helper3_planeCap_erase_iff A p (LinearMap.range B) D R ?_).mpr hcap
  rintro a ⟨u, rfl⟩
  exact congrArg (fun f : U →ₗ[F] F => f u) hzero

lemma helper3_planeCap_delete_data
    {F U S I J : Type*} [Field F] [AddCommGroup U] [Module F U]
    [AddCommGroup S] [Module F S] [Fintype I] [DecidableEq I]
    (A : I → S →ₗ[F] F) (p : J) (L : U →ₗ[F] (S × (J → F))) {D R : ℕ}
    (hcap : helper3_planeCap A
      (LinearMap.range ((LinearMap.fst F S (J → F)).comp L)) D R) :
    helper3_planeCap A
      (LinearMap.range ((LinearMap.fst F S ({j : J // j ≠ p} → F)).comp
        ((helper3_deleteData (K := F) p).comp L))) D R := hcap

open scoped BigOperators

def phaseSign (t : F) : ℤ := if t = 0 then 1 else -1

def codePhase {U S I J : Type} [AddCommGroup U] [Module F U]
    [AddCommGroup S] [Module F S] [Fintype I]
    (pos : I × Bool ↪ J) (A : I → S →ₗ[F] F) (h : S → F)
    (a : S × (J → F)) (L : U →ₗ[F] (S × (J → F))) (q : U → F) (x : U) : F :=
    q x + h (a + L x).1 + ∑ i : I, A i (a + L x).1 *
      (a + L x).2 (pos (i, false)) * (a + L x).2 (pos (i, true))

def TerminalFlatOracle (S : Type) [AddCommGroup S] [Module F S] (D R : ℕ) : Prop :=
  ∀ (U I J : Type) [AddCommGroup U] [Module F U] [FiniteDimensional F U]
    [Fintype U] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (pos : I × Bool ↪ J) (A : I → S →ₗ[F] F) (h : S → F)
    (a : S × (J → F)) (L : U →ₗ[F] (S × (J → F))) (q : U → F),
    Q2 q → Function.Injective L → Fintype.card J + 2 ≤ Module.finrank F U →
    helper3_planeCap A (LinearMap.range ((LinearMap.fst F S (J → F)).comp L)) D R →
    (∀ v : J → F, (0, v) ∈ LinearMap.range L) →
    D * (∑ x : U, phaseSign (codePhase pos A h a L q x)).natAbs ≤ R * Fintype.card U

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
lemma flat_upper_induction (S : Type) [AddCommGroup S] [Module F S] (D R : ℕ)
    (terminal : TerminalFlatOracle S D R) :
    ∀ (n : ℕ) (U I J : Type) [AddCommGroup U] [Module F U] [FiniteDimensional F U]
      [Fintype U] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J],
      Fintype.card J = n →
      ∀ (pos : I × Bool ↪ J) (A : I → S →ₗ[F] F) (h : S → F)
        (a : S × (J → F)) (L : U →ₗ[F] (S × (J → F))) (q : U → F),
      Q2 q → Function.Injective L → Fintype.card J + 2 ≤ Module.finrank F U →
      helper3_planeCap A (LinearMap.range ((LinearMap.fst F S (J → F)).comp L)) D R →
      D * (∑ x : U, phaseSign (codePhase pos A h a L q x)).natAbs ≤ R * Fintype.card U := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro U I J _ _ _ _ _ _ _ _ hn pos A h a L q hq hL hdim hcap
    rcases missing_data_axis_or_vertical (LinearMap.range L) with ⟨p, hp⟩ | hvertical
    · let J' := {j : J // j ≠ p}
      have hcard : Fintype.card J' + 1 = Fintype.card J := card_delete_coordinate p
      have hlt : Fintype.card J' < n := by omega
      let del := helper3_deleteData (K := F) (S := S) p
      by_cases hpair : ∃ ib : I × Bool, pos ib = p
      · obtain ⟨⟨i, b⟩, hib⟩ := hpair
        subst p
        let I' := {j : I // j ≠ i}
        let A' : I' → S →ₗ[F] F := fun j => A j.val
        let pos' : I' × Bool ↪ J' := deletePairEmbedding pos i b
        let ell : U →ₗ[F] F := (A i).comp ((LinearMap.fst F S (J → F)).comp L)
        rcases helper3_zero_or_normalized_vector ell with hzero | ⟨u0, hu0⟩
        · let L' : U →ₗ[F] (S × (J' → F)) := del.comp L
          have hstep := helper3_delete_step L hL (pos (i, b)) hp 2 hdim
          have hL' : Function.Injective L' := hstep.1
          have hdim' : Fintype.card J' + 2 ≤ Module.finrank F U := by
            have hh := hstep.2.1
            omega
          have hcap' : helper3_planeCap A'
              (LinearMap.range ((LinearMap.fst F S (J' → F)).comp L')) D R :=
            helper3_planeCap_erase_zero_comp A i
              ((LinearMap.fst F S (J → F)).comp L) hcap hzero
          have hrow : ∀ x : U, A i (L ((LinearMap.id : U →ₗ[F] U) x)).1 = 0 := by
            intro x
            exact congrArg (fun f : U →ₗ[F] F => f x) hzero
          obtain ⟨q', hq', heq⟩ := pair_elimination_along_linear pos A h a L q hq
            i b 0 (LinearMap.id : U →ₗ[F] U) hrow
          have hphase (x : U) : codePhase pos A h a L q x =
              codePhase pos' A' h (del a) L' q' x := by
            simpa only [zero_add, map_zero, add_zero, LinearMap.id_apply,
              LinearMap.comp_id, codePhase] using heq x
          have hbound := ih (Fintype.card J') hlt U I' J' rfl
            pos' A' h (del a) L' q' hq' hL' hdim' hcap'
          have hsum : (∑ x : U, phaseSign (codePhase pos A h a L q x)) =
              ∑ x : U, phaseSign (codePhase pos' A' h (del a) L' q' x) :=
            Finset.sum_congr rfl (fun x _ => congrArg phaseSign (hphase x))
          rw [hsum]
          exact hbound
        · let K := LinearMap.ker ell
          let _ : Fintype K := Fintype.ofFinite K
          let L' : K →ₗ[F] (S × (J' → F)) := (del.comp L).comp K.subtype
          have hstep := helper3_split_delete_step L hL (pos (i, b)) hp ell 2 hdim
          have hL' : Function.Injective L' := hstep.1
          have hdim' : Fintype.card J' + 2 ≤ Module.finrank F K := hstep.2.1
          have hcap' : helper3_planeCap A'
              (LinearMap.range ((LinearMap.fst F S (J' → F)).comp L')) D R :=
            helper3_planeCap_split_delete A i (pos (i, b)) L hcap
          apply helper3_split_bound_aggregation ell u0 hu0
            (fun x => phaseSign (codePhase pos A h a L q x)) D R
          intro c
          have hrow : ∀ x : K, A i (L (K.subtype x)).1 = 0 := fun x => x.property
          obtain ⟨q', hq', heq⟩ := pair_elimination_along_linear pos A h a L q hq
            i b (c • u0) K.subtype hrow
          let a' : S × (J' → F) := del (a + L (c • u0))
          have hphase (x : K) : codePhase pos A h a L q (c • u0 + x.val) =
              codePhase pos' A' h a' L' q' x := heq x
          have hbound := ih (Fintype.card J') hlt K I' J' rfl
            pos' A' h a' L' q' hq' hL' hdim' hcap'
          have hsum : (∑ x : K, phaseSign (codePhase pos A h a L q (c • u0 + x.val))) =
              ∑ x : K, phaseSign (codePhase pos' A' h a' L' q' x) :=
            Finset.sum_congr rfl (fun x _ => congrArg phaseSign (hphase x))
          rw [hsum]
          exact hbound
      · have hfree : ∀ ib : I × Bool, pos ib ≠ p := by
          intro ib he
          exact hpair ⟨ib, he⟩
        let pos' : I × Bool ↪ J' := deleteFreeEmbedding pos p hfree
        let L' : U →ₗ[F] (S × (J' → F)) := del.comp L
        have hstep := helper3_delete_step L hL p hp 2 hdim
        have hL' : Function.Injective L' := hstep.1
        have hdim' : Fintype.card J' + 2 ≤ Module.finrank F U := by
          have hh := hstep.2.1
          omega
        have hcap' : helper3_planeCap A
            (LinearMap.range ((LinearMap.fst F S (J' → F)).comp L')) D R :=
          helper3_planeCap_delete_data A p L hcap
        have hbound := ih (Fintype.card J') hlt U I J' rfl
          pos' A h (del a) L' q hq hL' hdim' hcap'
        exact hbound
    · exact terminal U I J pos A h a L q hq hL hdim hcap hvertical

lemma flat_upper_of_terminal (S : Type) [AddCommGroup S] [Module F S] (D R : ℕ)
    (terminal : TerminalFlatOracle S D R)
    (U I J : Type) [AddCommGroup U] [Module F U] [FiniteDimensional F U]
    [Fintype U] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (pos : I × Bool ↪ J) (A : I → S →ₗ[F] F) (h : S → F)
    (a : S × (J → F)) (L : U →ₗ[F] (S × (J → F))) (q : U → F)
    (hq : Q2 q) (hL : Function.Injective L) (hdim : Fintype.card J + 2 ≤ Module.finrank F U)
    (hcap : helper3_planeCap A
      (LinearMap.range ((LinearMap.fst F S (J → F)).comp L)) D R) :
    D * (∑ x : U, phaseSign (codePhase pos A h a L q x)).natAbs ≤ R * Fintype.card U := by
  exact flat_upper_induction S D R terminal (Fintype.card J) U I J rfl
    pos A h a L q hq hL hdim hcap


lemma helper3_dyadic_scaled (m w : ℕ) (hw : w ≤ m) :
    (2 : ℚ) ^ m * (1 / 2 : ℚ) ^ w = (2 : ℚ) ^ (m - w) := by
  have he : (2 : ℚ) ^ m = (2 : ℚ) ^ (m - w) * (2 : ℚ) ^ w := by
    rw [← pow_add, Nat.sub_add_cancel hw]
  rw [he, mul_assoc, ← mul_pow]
  norm_num

noncomputable def helper3_planeNat
    {F S I : Type*} [Field F] [AddCommGroup S] [Module F S]
    [Fintype S] [Fintype I] [DecidableEq I]
    (A : I → S →ₗ[F] F) : ℕ := by
  classical
  exact (Finset.univ : Finset (S × S)).sup (fun w =>
    if w.1 ≠ 0 ∧ w.2 ≠ 0 ∧ w.1 ≠ w.2 then
      2 ^ Fintype.card I + 2 ^ (Fintype.card I - helper3_codeWeight A w.1) +
        2 ^ (Fintype.card I - helper3_codeWeight A w.2) +
        2 ^ (Fintype.card I - helper3_codeWeight A (w.1 + w.2)) else 0)

lemma helper3_posted_planeCap
    {F S I : Type*} [Field F] [AddCommGroup S] [Module F S]
    [Fintype S] [Fintype I] [DecidableEq I]
    (A : I → S →ₗ[F] F) (T : Submodule F S) :
    helper3_planeCap A T (2 ^ (Fintype.card I + 2)) (helper3_planeNat A) := by
  classical
  intro a b _ _ ha hb hab
  have hsup : 2 ^ Fintype.card I + 2 ^ (Fintype.card I - helper3_codeWeight A a) +
      2 ^ (Fintype.card I - helper3_codeWeight A b) +
      2 ^ (Fintype.card I - helper3_codeWeight A (a + b)) ≤ helper3_planeNat A := by
    have hh := Finset.le_sup (f := fun w : S × S =>
      if w.1 ≠ 0 ∧ w.2 ≠ 0 ∧ w.1 ≠ w.2 then
        2 ^ Fintype.card I + 2 ^ (Fintype.card I - helper3_codeWeight A w.1) +
          2 ^ (Fintype.card I - helper3_codeWeight A w.2) +
          2 ^ (Fintype.card I - helper3_codeWeight A (w.1 + w.2)) else 0)
      (Finset.mem_univ (a, b))
    simpa [helper3_planeNat, ha, hb, hab] using hh
  have hw (x : S) : helper3_codeWeight A x ≤ Fintype.card I := by
    unfold helper3_codeWeight
    exact (Finset.card_filter_le _ _).trans_eq (Finset.card_univ)
  have hsupQ : (2 : ℚ) ^ Fintype.card I + 2 ^ (Fintype.card I - helper3_codeWeight A a) +
      2 ^ (Fintype.card I - helper3_codeWeight A b) +
      2 ^ (Fintype.card I - helper3_codeWeight A (a + b)) ≤ helper3_planeNat A := by
    exact_mod_cast hsup
  norm_num only [Nat.cast_pow, Nat.cast_ofNat]
  calc
    (2 : ℚ) ^ (Fintype.card I + 2) *
        (1 + (1 / 2 : ℚ) ^ helper3_codeWeight A a +
          (1 / 2 : ℚ) ^ helper3_codeWeight A b +
          (1 / 2 : ℚ) ^ helper3_codeWeight A (a + b)) =
        4 * ((2 : ℚ) ^ Fintype.card I *
          (1 + (1 / 2 : ℚ) ^ helper3_codeWeight A a +
            (1 / 2 : ℚ) ^ helper3_codeWeight A b +
            (1 / 2 : ℚ) ^ helper3_codeWeight A (a + b))) := by
      rw [pow_add]
      norm_num
      ring
    _ = 4 * ((2 : ℚ) ^ Fintype.card I +
        2 ^ (Fintype.card I - helper3_codeWeight A a) +
        2 ^ (Fintype.card I - helper3_codeWeight A b) +
        2 ^ (Fintype.card I - helper3_codeWeight A (a + b))) := by
      congr 1
      simp only [mul_add, mul_one]
      rw [
        helper3_dyadic_scaled _ _ (hw a), helper3_dyadic_scaled _ _ (hw b),
        helper3_dyadic_scaled _ _ (hw (a + b))]
    _ ≤ 4 * (helper3_planeNat A : ℚ) := mul_le_mul_of_nonneg_left hsupQ (by norm_num)




abbrev FlatDataIndex (m r : ℕ) := (Fin m × Bool) ⊕ Fin r

def dataCoordinates (m r : ℕ) :
    (FlatDataIndex m r → F) ≃ₗ[F] (Fin m → F) × ((Fin m → F) × (Fin r → F)) where
  toFun z := ((fun i => z (Sum.inl (i, false))),
    (fun i => z (Sum.inl (i, true))), (fun j => z (Sum.inr j)))
  invFun q j := match j with
    | Sum.inl (i, false) => q.1 i
    | Sum.inl (i, true) => q.2.1 i
    | Sum.inr j => q.2.2 j
  left_inv z := by
    funext j
    cases j with
    | inl j => rcases j with ⟨i, b⟩; cases b <;> rfl
    | inr j => rfl
  right_inv q := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma dataCoordinates_false (m r : ℕ) (z : FlatDataIndex m r → F) (i : Fin m) :
    (dataCoordinates m r z).1 i = z (Sum.inl (i, false)) := rfl

lemma dataCoordinates_true (m r : ℕ) (z : FlatDataIndex m r → F) (i : Fin m) :
    (dataCoordinates m r z).2.1 i = z (Sum.inl (i, true)) := rfl

lemma dataCoordinates_free (m r : ℕ) (z : FlatDataIndex m r → F) (j : Fin r) :
    (dataCoordinates m r z).2.2 j = z (Sum.inr j) := rfl

lemma dataCoordinates_symm_false (m r : ℕ)
    (q : (Fin m → F) × ((Fin m → F) × (Fin r → F))) (i : Fin m) :
    (dataCoordinates m r).symm q (Sum.inl (i, false)) = q.1 i := rfl

lemma dataCoordinates_symm_true (m r : ℕ)
    (q : (Fin m → F) × ((Fin m → F) × (Fin r → F))) (i : Fin m) :
    (dataCoordinates m r).symm q (Sum.inl (i, true)) = q.2.1 i := rfl

lemma dataCoordinates_symm_free (m r : ℕ)
    (q : (Fin m → F) × ((Fin m → F) × (Fin r → F))) (j : Fin r) :
    (dataCoordinates m r).symm q (Sum.inr j) = q.2.2 j := rfl

def flatPairEmbedding (m r : ℕ) : Fin m × Bool ↪ FlatDataIndex m r where
  toFun := Sum.inl
  inj' := by intro x y h; cases h; rfl

lemma flatPairEmbedding_apply (m r : ℕ) (i : Fin m × Bool) :
    flatPairEmbedding m r i = Sum.inl i := rfl

lemma flatPairEmbedding_ne_free (m r : ℕ) (i : Fin m × Bool) (j : Fin r) :
    flatPairEmbedding m r i ≠ Sum.inr j := by
  intro h
  cases h

lemma card_flatDataIndex (m r : ℕ) : Fintype.card (FlatDataIndex m r) = 2 * m + r := by
  simp [FlatDataIndex, Nat.mul_comm]

def eFlat {V S : Type} [AddCommGroup V] [Module F V]
    [AddCommGroup S] [Module F S] (m r : ℕ)
    (e : V ≃ₗ[F] S × ((Fin m → F) × ((Fin m → F) × (Fin r → F)))) :
    V ≃ₗ[F] S × (FlatDataIndex m r → F) :=
  e.trans (LinearEquiv.prodCongr (LinearEquiv.refl F S) (dataCoordinates m r).symm)

lemma eFlat_injective {V S : Type} [AddCommGroup V] [Module F V]
    [AddCommGroup S] [Module F S] (m r : ℕ)
    (e : V ≃ₗ[F] S × ((Fin m → F) × ((Fin m → F) × (Fin r → F)))) :
    Function.Injective (eFlat m r e) := (eFlat m r e).injective

lemma eFlat_selector {V S : Type} [AddCommGroup V] [Module F V]
    [AddCommGroup S] [Module F S] (m r : ℕ)
    (e : V ≃ₗ[F] S × ((Fin m → F) × ((Fin m → F) × (Fin r → F)))) (x : V) :
    (eFlat m r e x).1 = (e x).1 := rfl

lemma eFlat_false {V S : Type} [AddCommGroup V] [Module F V]
    [AddCommGroup S] [Module F S] (m r : ℕ)
    (e : V ≃ₗ[F] S × ((Fin m → F) × ((Fin m → F) × (Fin r → F))))
    (x : V) (i : Fin m) :
    (eFlat m r e x).2 (flatPairEmbedding m r (i, false)) = (e x).2.1 i := rfl

lemma eFlat_true {V S : Type} [AddCommGroup V] [Module F V]
    [AddCommGroup S] [Module F S] (m r : ℕ)
    (e : V ≃ₗ[F] S × ((Fin m → F) × ((Fin m → F) × (Fin r → F))))
    (x : V) (i : Fin m) :
    (eFlat m r e x).2 (flatPairEmbedding m r (i, true)) = (e x).2.2.1 i := rfl

lemma eFlat_free {V S : Type} [AddCommGroup V] [Module F V]
    [AddCommGroup S] [Module F S] (m r : ℕ)
    (e : V ≃ₗ[F] S × ((Fin m → F) × ((Fin m → F) × (Fin r → F))))
    (x : V) (j : Fin r) :
    (eFlat m r e x).2 (Sum.inr j) = (e x).2.2.2 j := rfl



open scoped BigOperators

def IsQuad {ι : Type} [Fintype ι] (Q : (ι → F) → F) : Prop :=
  ∃ (M : ι → ι → F) (c : F), ∀ y, Q y = (∑ i, ∑ j, M i j * y i * y j) + c

def PostedQuad {ι : Type} [Fintype ι] (q : (ι → F) → F) : Prop :=
  ∃ (z : F) (l : ι → F) (M : ι → ι → F),
    ∀ x, q x = z + dotProduct l x + ∑ i, ∑ j, M i j * x i * x j

lemma zmod2_mul_self_bridge (a : F) : a * a = a := by
  fin_cases a <;> rfl

lemma postedQuad_iff_isQuad {ι : Type} [Fintype ι] (q : (ι → F) → F) :
    PostedQuad q ↔ IsQuad q := by
  classical
  constructor
  · rintro ⟨z, l, M, h⟩
    refine ⟨fun i j => M i j + if i = j then l i else 0, z, fun x => ?_⟩
    rw [h x]
    have hdiag : (∑ i, ∑ j, (if i = j then l i else 0) * x i * x j) = dotProduct l x := by
      unfold dotProduct
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_eq_single i]
      · simp only [ite_true, mul_assoc, zmod2_mul_self_bridge]
      · intro j _ hji
        simp [Ne.symm hji]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    simp only [add_mul, Finset.sum_add_distrib]
    rw [hdiag]
    ring
  · rintro ⟨M, c, h⟩
    refine ⟨c, 0, M, fun x => ?_⟩
    rw [h x]
    simp only [zero_dotProduct, add_zero]
    exact add_comm _ _

lemma isQuad_implies_q2 {ι : Type} [Fintype ι] {q : (ι → F) → F}
    (hq : IsQuad q) : Q2 q := by
  classical
  obtain ⟨M, c, hq⟩ := hq
  refine ⟨c, 0,
    ∑ i, ∑ j, (M i j • (LinearMap.proj i : (ι → F) →ₗ[F] F)).smulRight
      (LinearMap.proj j : (ι → F) →ₗ[F] F), fun x => ?_⟩
  rw [hq x]
  simp only [LinearMap.zero_apply, add_zero, LinearMap.sum_apply,
    LinearMap.smulRight_apply, LinearMap.smul_apply, smul_eq_mul]
  exact add_comm _ _

def dotRow {ι : Type} [Fintype ι] (v : ι → F) : (ι → F) →ₗ[F] F :=
  ∑ i, v i • (LinearMap.proj i : (ι → F) →ₗ[F] F)

lemma dotRow_apply {ι : Type} [Fintype ι] (v x : ι → F) :
    dotRow v x = dotProduct v x := by
  simp [dotRow, dotProduct]

lemma phaseSign_add_agreement (a b : F) :
    phaseSign (a + b) = (if b = a then (1 : ℤ) else -1) := by
  fin_cases a <;> fin_cases b <;> rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1200000 in
lemma original_flat_upper_of_terminal (k m r : ℕ)
    (e : (Fin (k + 2 * m + r) → F) ≃ₗ[F]
      (Fin k → F) × ((Fin m → F) × ((Fin m → F) × (Fin r → F))))
    (A : Fin m → Fin k → F) (h : (Fin k → F) → F) :
    let wt := fun (a : Fin k → F) => ((Finset.univ : Finset (Fin m)).filter
      (fun i => dotProduct (A i) a ≠ 0)).card
    let g := fun (y : Fin (k + 2 * m + r) → F) => h (e y).1 + ∑ i : Fin m,
      dotProduct (A i) (e y).1 * (e y).2.1 i * (e y).2.2.1 i
    let b := 2 * m + r + 2
    let E := Fin b → F
    let quad := fun (q : E → F) => ∃ (z : F) (l : E) (M : Fin b → Fin b → F),
      ∀ x, q x = z + dotProduct l x + ∑ i, ∑ j, M i j * x i * x j
    let flat := fun (L : E →ₗ[F] (Fin (k + 2 * m + r) → F))
      (a : Fin (k + 2 * m + r) → F) (q : E → F) =>
      (∑ x : E, if g (a + L x) = q x then (1 : ℤ) else -1).natAbs
    let mass := fun (w : (Fin k → F) × (Fin k → F)) =>
      if w.1 ≠ 0 ∧ w.2 ≠ 0 ∧ w.1 ≠ w.2 then
        2 ^ m + 2 ^ (m - wt w.1) + 2 ^ (m - wt w.2) + 2 ^ (m - wt (w.1 + w.2)) else 0
    let plane := (Finset.univ : Finset ((Fin k → F) × (Fin k → F))).sup mass
    TerminalFlatOracle (Fin k → F) (2 ^ (m + 2)) plane →
      ∀ (L : E →ₗ[F] (Fin (k + 2 * m + r) → F))
        (a : Fin (k + 2 * m + r) → F) (q : E → F),
        Function.Injective L → quad q → 2 ^ (m + 2) * flat L a q ≤ 2 ^ b * plane := by
  classical
  dsimp only
  intro terminal L a q hL hq
  let b := 2 * m + r + 2
  let E := Fin b → F
  let S := Fin k → F
  let J := FlatDataIndex m r
  let row : Fin m → S →ₗ[F] F := fun i => dotRow (A i)
  let ef := eFlat m r e
  let LL := ef.toLinearMap.comp L
  let aa := ef a
  let g := fun (y : Fin (k + 2 * m + r) → F) => h (e y).1 + ∑ i : Fin m,
    dotProduct (A i) (e y).1 * (e y).2.1 i * (e y).2.2.1 i
  have hquad : Q2 q := isQuad_implies_q2 ((postedQuad_iff_isQuad q).mp hq)
  have hLL : Function.Injective LL := ef.injective.comp hL
  have hdim : Fintype.card J + 2 ≤ Module.finrank F E := by
    simp [J, E, b, Nat.mul_comm]
  have hcap := helper3_posted_planeCap row
    (LinearMap.range ((LinearMap.fst F S (J → F)).comp LL))
  have hplane : helper3_planeNat row =
      (Finset.univ : Finset (S × S)).sup (fun w =>
        if w.1 ≠ 0 ∧ w.2 ≠ 0 ∧ w.1 ≠ w.2 then
          2 ^ m + 2 ^ (m - ((Finset.univ : Finset (Fin m)).filter
            (fun i => dotProduct (A i) w.1 ≠ 0)).card) +
          2 ^ (m - ((Finset.univ : Finset (Fin m)).filter
            (fun i => dotProduct (A i) w.2 ≠ 0)).card) +
          2 ^ (m - ((Finset.univ : Finset (Fin m)).filter
            (fun i => dotProduct (A i) (w.1 + w.2) ≠ 0)).card) else 0) := by
    simp only [helper3_planeNat, helper3_codeWeight, Fintype.card_fin, row]
    simp only [dotRow, dotProduct, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul]
    rfl
  have hterminal : TerminalFlatOracle S (2 ^ (m + 2)) (helper3_planeNat row) := by
    rw [hplane]
    exact terminal
  have hbound := flat_upper_of_terminal S (2 ^ (m + 2)) (helper3_planeNat row)
    hterminal E (Fin m) J (flatPairEmbedding m r) row h aa LL q hquad hLL hdim
    (by simpa only [Fintype.card_fin] using hcap)
  have hphase (x : E) : phaseSign (codePhase (flatPairEmbedding m r) row h aa LL q x) =
      (if g (a + L x) = q x then (1 : ℤ) else -1) := by
    have heq : aa + LL x = ef (a + L x) := by
      simp [aa, LL, map_add]
    have hc : codePhase (flatPairEmbedding m r) row h aa LL q x = q x + g (a + L x) := by
      dsimp only [codePhase]
      rw [heq]
      simp only [ef, eFlat_selector, eFlat_false, eFlat_true]
      dsimp only [row, g]
      simp only [dotRow, dotProduct, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul]
      exact add_assoc _ _ _
    rw [hc]
    exact phaseSign_add_agreement _ _
  have hcard : Fintype.card E = 2 ^ b := by
    simp [E, F, ZMod.card]
  simp_rw [hphase] at hbound
  rw [hcard, hplane] at hbound
  simpa only [b, g, Nat.mul_comm] using hbound


def Q3prod {U : Type} [AddCommGroup U] [Module F U] (q : U → F) : Prop :=
  ∃ q0 f g h : U → F, Q2 q0 ∧ A1 f ∧ A1 g ∧ A1 h ∧
    ∀ x, q x = q0 x + f x * g x * h x

lemma q3prod_of_q2 {U : Type} [AddCommGroup U] [Module F U]
    {q : U → F} (hq : Q2 q) : Q3prod q := by
  refine ⟨q, fun _ => 0, fun _ => 0, fun _ => 0, hq,
    a1_const 0, a1_const 0, a1_const 0, ?_⟩
  intro x
  simp

lemma q3prod_comp_affine {U W : Type} [AddCommGroup U] [Module F U]
    [AddCommGroup W] [Module F W] {q : U → F} (hq : Q3prod q)
    (w : U) (B : W →ₗ[F] U) : Q3prod (fun x => q (w + B x)) := by
  obtain ⟨q0, f, g, h, hq0, hf, hg, hh, heq⟩ := hq
  exact ⟨fun x => q0 (w + B x), fun x => f (w + B x),
    fun x => g (w + B x), fun x => h (w + B x),
    q2_comp_affine hq0 w B, a1_comp_affine hf w B,
    a1_comp_affine hg w B, a1_comp_affine hh w B, fun x => heq (w + B x)⟩

lemma q3prod_add_q2 {U : Type} [AddCommGroup U] [Module F U]
    {q r : U → F} (hq : Q3prod q) (hr : Q2 r) : Q3prod (fun x => q x + r x) := by
  obtain ⟨q0, f, g, h, hq0, hf, hg, hh, heq⟩ := hq
  refine ⟨fun x => q0 x + r x, f, g, h, q2_add hq0 hr, hf, hg, hh, ?_⟩
  intro x
  dsimp only
  rw [heq x]
  ring
lemma pair_elimination_along_linear_q3
    {U W S I J : Type} [AddCommGroup U] [Module F U]
    [AddCommGroup W] [Module F W]
    [AddCommGroup S] [Module F S] [Fintype I] [DecidableEq I]
    (pos : I × Bool ↪ J) (A : I → S →ₗ[F] F) (h : S → F)
    (a : S × (J → F)) (L : U →ₗ[F] (S × (J → F)))
    (q : U → F) (hq : Q3prod q) (i : I) (b : Bool) (w : U)
    (B : W →ₗ[F] U) (hB : ∀ x, A i (L (B x)).1 = 0) :
    let del := helper3_deleteData (K := F) (S := S) (pos (i, b))
    let a' := del (a + L w)
    let L' := (del.comp L).comp B
    ∃ q' : W → F, Q3prod q' ∧ ∀ x : W,
      q (w + (B x)) + h (a + L (w + (B x))).1 +
          ∑ j, A j (a + L (w + (B x))).1 *
            (a + L (w + (B x))).2 (pos (j, false)) *
            (a + L (w + (B x))).2 (pos (j, true)) =
        q' x + h (a' + L' x).1 +
          ∑ j : {j : I // j ≠ i}, A j.val (a' + L' x).1 *
            (a' + L' x).2 (deletePairEmbedding pos i b (j, false)) *
            (a' + L' x).2 (deletePairEmbedding pos i b (j, true)) := by
  dsimp only
  let c := A i (a + L w).1
  let u : W → F := fun x => (a + L (w + (B x))).2 (pos (i, false))
  let v : W → F := fun x => (a + L (w + (B x))).2 (pos (i, true))
  have hu : A1 u :=
    a1_comp_affine (a1_data_coordinate a L (pos (i, false))) w B
  have hv : A1 v :=
    a1_comp_affine (a1_data_coordinate a L (pos (i, true))) w B
  refine ⟨fun x => q (w + (B x)) + c * u x * v x,
    q3prod_add_q2 (q3prod_comp_affine hq w B) (q2_mul_a1 (a1_smul c hu) hv), ?_⟩
  intro x
  have hc : A i (a + L (w + (B x))).1 = c := by
    have hx : A i (L (B x)).1 = 0 := hB x
    simp [c, map_add, hx]
  have hy : a + L (w + (B x)) = a + L w + L (B x) := by
    rw [map_add, add_assoc]
  have hyu : u x = (a + L w + L (B x)).2 (pos (i, false)) := by
    dsimp only [u]
    rw [hy]
  have hyv : v x = (a + L w + L (B x)).2 (pos (i, true)) := by
    dsimp only [v]
    rw [hy]
  rw [hy] at hc ⊢
  rw [basisfree_sum_delete i, hc]
  change q (w + (B x)) + h (a + L w + L (B x)).1 +
      (c * (a + L w + L (B x)).2 (pos (i, false)) *
        (a + L w + L (B x)).2 (pos (i, true)) +
        ∑ j : {j : I // j ≠ i}, A j.val (a + L w + L (B x)).1 *
          (a + L w + L (B x)).2 (pos (j.val, false)) *
          (a + L w + L (B x)).2 (pos (j.val, true))) =
      (q (w + (B x)) + c * u x * v x) + h (a + L w + L (B x)).1 +
        ∑ j : {j : I // j ≠ i}, A j.val (a + L w + L (B x)).1 *
          (a + L w + L (B x)).2 (pos (j.val, false)) *
          (a + L w + L (B x)).2 (pos (j.val, true))
  rw [hyu, hyv]
  ring


lemma free_coordinate_elimination_along_linear_q3
    {U W S I J : Type} [AddCommGroup U] [Module F U]
    [AddCommGroup W] [Module F W] [AddCommGroup S] [Module F S]
    [Fintype I]
    (pos : I × Bool ↪ J) (A : I → S →ₗ[F] F) (h : S → F)
    (a : S × (J → F)) (L : U →ₗ[F] (S × (J → F)))
    (q : U → F) (hq : Q3prod q) (p : J) (hp : ∀ i, pos i ≠ p)
    (w : U) (B : W →ₗ[F] U) :
    let del := helper3_deleteData (K := F) (S := S) p
    let a' := del (a + L w)
    let L' := (del.comp L).comp B
    ∃ q' : W → F, Q3prod q' ∧ ∀ x : W,
      q (w + B x) + h (a + L (w + B x)).1 +
          ∑ j, A j (a + L (w + B x)).1 *
            (a + L (w + B x)).2 (pos (j, false)) *
            (a + L (w + B x)).2 (pos (j, true)) =
        q' x + h (a' + L' x).1 +
          ∑ j, A j (a' + L' x).1 *
            (a' + L' x).2 (deleteFreeEmbedding pos p hp (j, false)) *
            (a' + L' x).2 (deleteFreeEmbedding pos p hp (j, true)) := by
  dsimp only
  refine ⟨fun x => q (w + B x), q3prod_comp_affine hq w B, fun x => ?_⟩
  have hy : a + L (w + B x) = a + L w + L (B x) := by
    rw [map_add, add_assoc]
  rw [hy]
  rfl


noncomputable def minWeightCap
    {S I : Type} [AddCommGroup S] [Module F S] [Fintype I] [DecidableEq I]
    (A : I → S →ₗ[F] F) (T : Submodule F S) (d : ℕ) : Prop :=
    ∀ a : S, a ∈ T → a ≠ 0 → d ≤ helper3_codeWeight A a

lemma minWeightCap_mono
    {S I : Type} [AddCommGroup S] [Module F S] [Fintype I] [DecidableEq I]
    (A : I → S →ₗ[F] F) {T T' : Submodule F S} {d : ℕ}
    (hcap : minWeightCap A T d) (hT : T' ≤ T) : minWeightCap A T' d := by
  intro a ha hna
  exact hcap a (hT ha) hna

lemma minWeightCap_erase_iff
    {S I : Type} [AddCommGroup S] [Module F S] [Fintype I] [DecidableEq I]
    (A : I → S →ₗ[F] F) (p : I) (T : Submodule F S) (d : ℕ)
    (hp : ∀ a ∈ T, A p a = 0) :
    minWeightCap (fun i : {i : I // i ≠ p} => A i.val) T d ↔ minWeightCap A T d := by
  constructor <;> intro h a ha hna
  · have hh := h a ha hna
    rw [helper3_codeWeight_erase_eq A p a (hp a ha)] at hh
    exact hh
  · rw [helper3_codeWeight_erase_eq A p a (hp a ha)]
    exact h a ha hna

lemma minWeightCap_erase_mono
    {S I : Type} [AddCommGroup S] [Module F S] [Fintype I] [DecidableEq I]
    (A : I → S →ₗ[F] F) (p : I) {T T' : Submodule F S} {d : ℕ}
    (hcap : minWeightCap A T d) (hT : T' ≤ T) (hp : ∀ a ∈ T', A p a = 0) :
    minWeightCap (fun i : {i : I // i ≠ p} => A i.val) T' d := by
  apply (minWeightCap_erase_iff A p T' d hp).mpr
  exact minWeightCap_mono A hcap hT

lemma minWeightCap_split_erase
    {U S I : Type} [AddCommGroup U] [Module F U]
    [AddCommGroup S] [Module F S] [Fintype I] [DecidableEq I]
    (A : I → S →ₗ[F] F) (p : I) (B : U →ₗ[F] S) {d : ℕ}
    (hcap : minWeightCap A (LinearMap.range B) d) :
    minWeightCap (fun i : {i : I // i ≠ p} => A i.val)
      (LinearMap.range (B.comp (LinearMap.ker ((A p).comp B)).subtype)) d := by
  apply minWeightCap_erase_mono A p hcap
  · rintro a ⟨u, rfl⟩
    exact ⟨u.val, rfl⟩
  · rintro a ⟨u, rfl⟩
    exact u.property

lemma minWeightCap_split_delete
    {U S I J : Type} [AddCommGroup U] [Module F U]
    [AddCommGroup S] [Module F S] [Fintype I] [DecidableEq I]
    (A : I → S →ₗ[F] F) (i : I) (p : J) (L : U →ₗ[F] (S × (J → F))) {d : ℕ}
    (hcap : minWeightCap A
      (LinearMap.range ((LinearMap.fst F S (J → F)).comp L)) d) :
    let B := (LinearMap.fst F S (J → F)).comp L
    let L' := ((helper3_deleteData (K := F) p).comp L).comp
      (LinearMap.ker ((A i).comp B)).subtype
    minWeightCap (fun j : {j : I // j ≠ i} => A j.val)
      (LinearMap.range ((LinearMap.fst F S ({j : J // j ≠ p} → F)).comp L')) d := by
  dsimp only
  exact minWeightCap_split_erase A i ((LinearMap.fst F S (J → F)).comp L) hcap

lemma minWeightCap_erase_zero_comp
    {U S I : Type} [AddCommGroup U] [Module F U]
    [AddCommGroup S] [Module F S] [Fintype I] [DecidableEq I]
    (A : I → S →ₗ[F] F) (p : I) (B : U →ₗ[F] S) {d : ℕ}
    (hcap : minWeightCap A (LinearMap.range B) d) (hzero : (A p).comp B = 0) :
    minWeightCap (fun i : {i : I // i ≠ p} => A i.val) (LinearMap.range B) d := by
  apply (minWeightCap_erase_iff A p (LinearMap.range B) d ?_).mpr hcap
  rintro a ⟨u, rfl⟩
  exact congrArg (fun f : U →ₗ[F] F => f u) hzero

lemma minWeightCap_delete_data
    {U S I J : Type} [AddCommGroup U] [Module F U]
    [AddCommGroup S] [Module F S] [Fintype I] [DecidableEq I]
    (A : I → S →ₗ[F] F) (p : J) (L : U →ₗ[F] (S × (J → F))) {d : ℕ}
    (hcap : minWeightCap A
      (LinearMap.range ((LinearMap.fst F S (J → F)).comp L)) d) :
    minWeightCap A
      (LinearMap.range ((LinearMap.fst F S ({j : J // j ≠ p} → F)).comp
        ((helper3_deleteData (K := F) p).comp L))) d := hcap
def TerminalLineOracle (S : Type) [AddCommGroup S] [Module F S] (d D R : ℕ) : Prop :=
  ∀ (U I J : Type) [AddCommGroup U] [Module F U] [FiniteDimensional F U]
    [Fintype U] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (pos : I × Bool ↪ J) (A : I → S →ₗ[F] F) (h : S → F)
    (a : S × (J → F)) (L : U →ₗ[F] (S × (J → F))) (q : U → F),
    Q3prod q → Function.Injective L → Fintype.card J + 1 ≤ Module.finrank F U →
    minWeightCap A (LinearMap.range ((LinearMap.fst F S (J → F)).comp L)) d →
    (∀ v : J → F, (0, v) ∈ LinearMap.range L) →
    D * (∑ x : U, phaseSign (codePhase pos A h a L q x)).natAbs ≤ R * Fintype.card U

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
lemma line_upper_induction (S : Type) [AddCommGroup S] [Module F S] (d D R : ℕ)
    (terminal : TerminalLineOracle S d D R) :
    ∀ (n : ℕ) (U I J : Type) [AddCommGroup U] [Module F U] [FiniteDimensional F U]
      [Fintype U] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J],
      Fintype.card J = n →
      ∀ (pos : I × Bool ↪ J) (A : I → S →ₗ[F] F) (h : S → F)
        (a : S × (J → F)) (L : U →ₗ[F] (S × (J → F))) (q : U → F),
      Q3prod q → Function.Injective L → Fintype.card J + 1 ≤ Module.finrank F U →
      minWeightCap A (LinearMap.range ((LinearMap.fst F S (J → F)).comp L)) d →
      D * (∑ x : U, phaseSign (codePhase pos A h a L q x)).natAbs ≤ R * Fintype.card U := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro U I J _ _ _ _ _ _ _ _ hn pos A h a L q hq hL hdim hcap
    rcases missing_data_axis_or_vertical (LinearMap.range L) with ⟨p, hp⟩ | hvertical
    · let J' := {j : J // j ≠ p}
      have hcard : Fintype.card J' + 1 = Fintype.card J := card_delete_coordinate p
      have hlt : Fintype.card J' < n := by omega
      let del := helper3_deleteData (K := F) (S := S) p
      by_cases hpair : ∃ ib : I × Bool, pos ib = p
      · obtain ⟨⟨i, b⟩, hib⟩ := hpair
        subst p
        let I' := {j : I // j ≠ i}
        let A' : I' → S →ₗ[F] F := fun j => A j.val
        let pos' : I' × Bool ↪ J' := deletePairEmbedding pos i b
        let ell : U →ₗ[F] F := (A i).comp ((LinearMap.fst F S (J → F)).comp L)
        rcases helper3_zero_or_normalized_vector ell with hzero | ⟨u0, hu0⟩
        · let L' : U →ₗ[F] (S × (J' → F)) := del.comp L
          have hstep := helper3_delete_step L hL (pos (i, b)) hp 1 hdim
          have hL' : Function.Injective L' := hstep.1
          have hdim' : Fintype.card J' + 1 ≤ Module.finrank F U := by
            have hh := hstep.2.1
            omega
          have hcap' : minWeightCap A'
              (LinearMap.range ((LinearMap.fst F S (J' → F)).comp L')) d :=
            minWeightCap_erase_zero_comp A i
              ((LinearMap.fst F S (J → F)).comp L) hcap hzero
          have hrow : ∀ x : U, A i (L ((LinearMap.id : U →ₗ[F] U) x)).1 = 0 := by
            intro x
            exact congrArg (fun f : U →ₗ[F] F => f x) hzero
          obtain ⟨q', hq', heq⟩ := pair_elimination_along_linear_q3 pos A h a L q hq
            i b 0 (LinearMap.id : U →ₗ[F] U) hrow
          have hphase (x : U) : codePhase pos A h a L q x =
              codePhase pos' A' h (del a) L' q' x := by
            simpa only [zero_add, map_zero, add_zero, LinearMap.id_apply,
              LinearMap.comp_id, codePhase] using heq x
          have hbound := ih (Fintype.card J') hlt U I' J' rfl
            pos' A' h (del a) L' q' hq' hL' hdim' hcap'
          have hsum : (∑ x : U, phaseSign (codePhase pos A h a L q x)) =
              ∑ x : U, phaseSign (codePhase pos' A' h (del a) L' q' x) :=
            Finset.sum_congr rfl (fun x _ => congrArg phaseSign (hphase x))
          rw [hsum]
          exact hbound
        · let K := LinearMap.ker ell
          let _ : Fintype K := Fintype.ofFinite K
          let L' : K →ₗ[F] (S × (J' → F)) := (del.comp L).comp K.subtype
          have hstep := helper3_split_delete_step L hL (pos (i, b)) hp ell 1 hdim
          have hL' : Function.Injective L' := hstep.1
          have hdim' : Fintype.card J' + 1 ≤ Module.finrank F K := hstep.2.1
          have hcap' : minWeightCap A'
              (LinearMap.range ((LinearMap.fst F S (J' → F)).comp L')) d :=
            minWeightCap_split_delete A i (pos (i, b)) L hcap
          apply helper3_split_bound_aggregation ell u0 hu0
            (fun x => phaseSign (codePhase pos A h a L q x)) D R
          intro c
          have hrow : ∀ x : K, A i (L (K.subtype x)).1 = 0 := fun x => x.property
          obtain ⟨q', hq', heq⟩ := pair_elimination_along_linear_q3 pos A h a L q hq
            i b (c • u0) K.subtype hrow
          let a' : S × (J' → F) := del (a + L (c • u0))
          have hphase (x : K) : codePhase pos A h a L q (c • u0 + x.val) =
              codePhase pos' A' h a' L' q' x := heq x
          have hbound := ih (Fintype.card J') hlt K I' J' rfl
            pos' A' h a' L' q' hq' hL' hdim' hcap'
          have hsum : (∑ x : K, phaseSign (codePhase pos A h a L q (c • u0 + x.val))) =
              ∑ x : K, phaseSign (codePhase pos' A' h a' L' q' x) :=
            Finset.sum_congr rfl (fun x _ => congrArg phaseSign (hphase x))
          rw [hsum]
          exact hbound
      · have hfree : ∀ ib : I × Bool, pos ib ≠ p := by
          intro ib he
          exact hpair ⟨ib, he⟩
        let pos' : I × Bool ↪ J' := deleteFreeEmbedding pos p hfree
        let L' : U →ₗ[F] (S × (J' → F)) := del.comp L
        have hstep := helper3_delete_step L hL p hp 1 hdim
        have hL' : Function.Injective L' := hstep.1
        have hdim' : Fintype.card J' + 1 ≤ Module.finrank F U := by
          have hh := hstep.2.1
          omega
        have hcap' : minWeightCap A
            (LinearMap.range ((LinearMap.fst F S (J' → F)).comp L')) d :=
          minWeightCap_delete_data A p L hcap
        have hbound := ih (Fintype.card J') hlt U I J' rfl
          pos' A h (del a) L' q hq hL' hdim' hcap'
        exact hbound
    · exact terminal U I J pos A h a L q hq hL hdim hcap hvertical

lemma line_upper_of_terminal (S : Type) [AddCommGroup S] [Module F S] (d D R : ℕ)
    (terminal : TerminalLineOracle S d D R)
    (U I J : Type) [AddCommGroup U] [Module F U] [FiniteDimensional F U]
    [Fintype U] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (pos : I × Bool ↪ J) (A : I → S →ₗ[F] F) (h : S → F)
    (a : S × (J → F)) (L : U →ₗ[F] (S × (J → F))) (q : U → F)
    (hq : Q3prod q) (hL : Function.Injective L) (hdim : Fintype.card J + 1 ≤ Module.finrank F U)
    (hcap : minWeightCap A
      (LinearMap.range ((LinearMap.fst F S (J → F)).comp L)) d) :
    D * (∑ x : U, phaseSign (codePhase pos A h a L q x)).natAbs ≤ R * Fintype.card U := by
  exact line_upper_induction S d D R terminal (Fintype.card J) U I J rfl
    pos A h a L q hq hL hdim hcap



lemma a1_of_affineMap {U : Type} [AddCommGroup U] [Module F U]
    (f : U →ᵃ[F] F) : A1 f := by
  refine ⟨f 0, f.linear, fun x => ?_⟩
  have hh := f.map_vadd (0 : U) x
  simpa only [vadd_eq_add, add_zero, add_comm] using hh

lemma line_bound_rescale (m d b N : ℕ) (hd : 0 < d) (hdm : d ≤ m)
    (hbound : 2 ^ d * N ≤ (2 ^ (d - 1) + 1) * 2 ^ b) :
    2 ^ (m + 2) * N ≤ 2 ^ (b + 1) * (2 ^ m + 2 ^ (m + 1 - d)) := by
  have hleft : (2 : ℕ) ^ (m + 2 - d) * 2 ^ d = 2 ^ (m + 2) := by
    rw [← pow_add]
    congr 1
    omega
  have hcross : (2 : ℕ) ^ (m + 2 - d) * 2 ^ (d - 1) = 2 ^ (m + 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hshift : (2 : ℕ) ^ (m + 2 - d) = 2 ^ (m + 1 - d) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  calc
    2 ^ (m + 2) * N = 2 ^ (m + 2 - d) * (2 ^ d * N) := by
      rw [← mul_assoc, hleft]
    _ ≤ 2 ^ (m + 2 - d) * ((2 ^ (d - 1) + 1) * 2 ^ b) :=
      Nat.mul_le_mul_left _ hbound
    _ = 2 ^ (b + 1) * (2 ^ m + 2 ^ (m + 1 - d)) := by
      rw [← mul_assoc, mul_add, mul_one, hcross, hshift, pow_succ (2 : ℕ) m, pow_succ (2 : ℕ) b]
      ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1200000 in
lemma original_line_upper_of_terminal (k m r d : ℕ) (hd : 0 < d) (hdm : d ≤ m)
    (e : (Fin (k + 2 * m + r) → F) ≃ₗ[F]
      (Fin k → F) × ((Fin m → F) × ((Fin m → F) × (Fin r → F))))
    (A : Fin m → Fin k → F) (h : (Fin k → F) → F)
    (hweight : ∀ a : Fin k → F, a ≠ 0 → d ≤
      ((Finset.univ : Finset (Fin m)).filter (fun i => dotProduct (A i) a ≠ 0)).card)
    (terminal : TerminalLineOracle (Fin k → F) d (2 ^ d) (2 ^ (d - 1) + 1)) :
    let g := fun (y : Fin (k + 2 * m + r) → F) => h (e y).1 + ∑ i : Fin m,
      dotProduct (A i) (e y).1 * (e y).2.1 i * (e y).2.2.1 i
    let b := 2 * m + r + 1
    let E := Fin b → F
    let quad := fun (q : E → F) => ∃ (z : F) (l : E) (M : Fin b → Fin b → F),
      ∀ x, q x = z + dotProduct l x + ∑ i, ∑ j, M i j * x i * x j
    ∀ (L : E →ₗ[F] (Fin (k + 2 * m + r) → F))
      (a : Fin (k + 2 * m + r) → F) (q : E → F) (u v w : E →ᵃ[F] F),
      Function.Injective L → quad q →
      2 ^ (m + 2) *
        (∑ x : E, if g (a + L x) = q x + u x * v x * w x then (1 : ℤ) else -1).natAbs ≤
      2 ^ (2 * m + r + 2) * (2 ^ m + 2 ^ (m + 1 - d)) := by
  classical
  dsimp only
  intro L a q u v w hL hq
  let b := 2 * m + r + 1
  let E := Fin b → F
  let S := Fin k → F
  let J := FlatDataIndex m r
  let row : Fin m → S →ₗ[F] F := fun i => dotRow (A i)
  let ef := eFlat m r e
  let LL := ef.toLinearMap.comp L
  let aa := ef a
  let qt := fun x : E => q x + u x * v x * w x
  let g := fun (y : Fin (k + 2 * m + r) → F) => h (e y).1 + ∑ i : Fin m,
    dotProduct (A i) (e y).1 * (e y).2.1 i * (e y).2.2.1 i
  have hquad : Q2 q := isQuad_implies_q2 ((postedQuad_iff_isQuad q).mp hq)
  have hqt : Q3prod qt := ⟨q, u, v, w, hquad, a1_of_affineMap u,
    a1_of_affineMap v, a1_of_affineMap w, fun x => rfl⟩
  have hLL : Function.Injective LL := ef.injective.comp hL
  have hdim : Fintype.card J + 1 ≤ Module.finrank F E := by
    simp [J, E, b, Nat.mul_comm]
  have hw_eq (z : S) : helper3_codeWeight row z =
      ((Finset.univ : Finset (Fin m)).filter (fun i => dotProduct (A i) z ≠ 0)).card := by
    simp only [helper3_codeWeight, row, dotRow, dotProduct, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul]
    rfl
  have hcap : minWeightCap row
      (LinearMap.range ((LinearMap.fst F S (J → F)).comp LL)) d := by
    intro z _ hz
    rw [hw_eq]
    exact hweight z hz
  have hbound := line_upper_of_terminal S d (2 ^ d) (2 ^ (d - 1) + 1)
    terminal E (Fin m) J (flatPairEmbedding m r) row h aa LL qt hqt hLL hdim hcap
  have hphase (x : E) : phaseSign (codePhase (flatPairEmbedding m r) row h aa LL qt x) =
      (if g (a + L x) = qt x then (1 : ℤ) else -1) := by
    have heq : aa + LL x = ef (a + L x) := by
      simp [aa, LL, map_add]
    have hc : codePhase (flatPairEmbedding m r) row h aa LL qt x = qt x + g (a + L x) := by
      dsimp only [codePhase]
      rw [heq]
      simp only [ef, eFlat_selector, eFlat_false, eFlat_true]
      dsimp only [row, g]
      simp only [dotRow, dotProduct, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
      exact add_assoc _ _ _
    rw [hc]
    exact phaseSign_add_agreement _ _
  have hcard : Fintype.card E = 2 ^ b := by
    simp [E, F, ZMod.card]
  simp_rw [hphase] at hbound
  rw [hcard] at hbound
  have hscaled := line_bound_rescale m d b _ hd hdm hbound
  have hb : b + 1 = 2 * m + r + 2 := rfl
  rw [hb] at hscaled
  exact hscaled




def selectorDataMap {F U S W : Type*} [Field F]
    [AddCommGroup U] [Module F U] [AddCommGroup S] [Module F S]
    [AddCommGroup W] [Module F W]
    (L : U →ₗ[F] S × W) :
    U →ₗ[F] LinearMap.range ((LinearMap.fst F S W).comp L) × W where
  toFun x := (⟨(L x).1, ⟨x, rfl⟩⟩, (L x).2)
  map_add' x y := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst (L.map_add x y)
    · exact congrArg (fun z : S × W => z.2) (L.map_add x y)
  map_smul' c x := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst (L.map_smul c x)
    · exact congrArg (fun z : S × W => z.2) (L.map_smul c x)

lemma selectorDataMap_bijective {F U S W : Type*} [Field F]
    [AddCommGroup U] [Module F U] [AddCommGroup S] [Module F S]
    [AddCommGroup W] [Module F W]
    (L : U →ₗ[F] S × W) (hL : Function.Injective L)
    (hvertical : ∀ w : W, (0, w) ∈ LinearMap.range L) :
    Function.Bijective (selectorDataMap L) := by
  constructor
  · intro x y h
    apply hL
    apply Prod.ext
    · exact congrArg (fun z => z.1.val) h
    · exact congrArg (fun z : LinearMap.range ((LinearMap.fst F S W).comp L) × W => z.2) h
  · rintro ⟨s, w⟩
    obtain ⟨x, hx⟩ := s.property
    change (L x).1 = s.val at hx
    obtain ⟨y, hy⟩ := hvertical (w - (L x).2)
    refine ⟨x + y, ?_⟩
    apply Prod.ext
    · apply Subtype.ext
      change (L (x + y)).1 = s.val
      rw [map_add, hy]
      simpa only [Prod.fst_add, add_zero] using hx
    · change (L (x + y)).2 = w
      rw [map_add, hy]
      simp

noncomputable def selectorDataEquiv {F U S W : Type*} [Field F]
    [AddCommGroup U] [Module F U] [AddCommGroup S] [Module F S]
    [AddCommGroup W] [Module F W]
    (L : U →ₗ[F] S × W) (hL : Function.Injective L)
    (hvertical : ∀ w : W, (0, w) ∈ LinearMap.range L) :
    U ≃ₗ[F] LinearMap.range ((LinearMap.fst F S W).comp L) × W :=
  LinearEquiv.ofBijective (selectorDataMap L) (selectorDataMap_bijective L hL hvertical)

lemma selectorDataEquiv_symm_coordinates {F U S W : Type*} [Field F]
    [AddCommGroup U] [Module F U] [AddCommGroup S] [Module F S]
    [AddCommGroup W] [Module F W]
    (L : U →ₗ[F] S × W) (hL : Function.Injective L)
    (hvertical : ∀ w : W, (0, w) ∈ LinearMap.range L)
    (s : LinearMap.range ((LinearMap.fst F S W).comp L)) (w : W) :
    L ((selectorDataEquiv L hL hvertical).symm (s, w)) = (s.val, w) := by
  have he := (selectorDataEquiv L hL hvertical).apply_symm_apply (s, w)
  apply Prod.ext
  · exact congrArg (fun z => z.1.val) he
  · exact congrArg (fun z : LinearMap.range ((LinearMap.fst F S W).comp L) × W => z.2) he

lemma selectorDataEquiv_affine_coordinates {F U S W : Type*} [Field F]
    [AddCommGroup U] [Module F U] [AddCommGroup S] [Module F S]
    [AddCommGroup W] [Module F W]
    (L : U →ₗ[F] S × W) (hL : Function.Injective L)
    (hvertical : ∀ w : W, (0, w) ∈ LinearMap.range L)
    (a : S × W) (s : LinearMap.range ((LinearMap.fst F S W).comp L)) (w : W) :
    a + L ((selectorDataEquiv L hL hvertical).symm (s, w)) =
      (a.1 + s.val, a.2 + w) := by
  rw [selectorDataEquiv_symm_coordinates]
  rfl

lemma selectorDataEquiv_surplus {F U S W : Type*} [Field F]
    [AddCommGroup U] [Module F U] [FiniteDimensional F U]
    [AddCommGroup S] [Module F S] [AddCommGroup W] [Module F W]
    [FiniteDimensional F W]
    (L : U →ₗ[F] S × W) (hL : Function.Injective L)
    (hvertical : ∀ w : W, (0, w) ∈ LinearMap.range L)
    (d : ℕ) (hdim : Module.finrank F W + d ≤ Module.finrank F U) :
    d ≤ Module.finrank F (LinearMap.range ((LinearMap.fst F S W).comp L)) := by
  have he := (selectorDataEquiv L hL hvertical).finrank_eq
  rw [Module.finrank_prod] at he
  omega

lemma selectorDataEquiv_sum {F U S W : Type*} [Field F]
    [AddCommGroup U] [Module F U] [AddCommGroup S] [Module F S]
    [AddCommGroup W] [Module F W] [Fintype U] [Fintype W]
    (L : U →ₗ[F] S × W) (hL : Function.Injective L)
    (hvertical : ∀ w : W, (0, w) ∈ LinearMap.range L)
    [Fintype (LinearMap.range ((LinearMap.fst F S W).comp L))]
    (f : U → ℤ) :
    (∑ x : U, f x) = ∑ s : LinearMap.range ((LinearMap.fst F S W).comp L),
      ∑ w : W, f ((selectorDataEquiv L hL hvertical).symm (s, w)) := by
  rw [← (selectorDataEquiv L hL hvertical).symm.toEquiv.sum_comp f,
    Fintype.sum_prod_type]
  rfl

end PEqualNP.Outside.L_meta_32057_aux

namespace PEqualNP.Outside.L_meta_32057_aux

lemma range_add_eq_sup_of_finrank_eq
    {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (A B : V →ₗ[K] W)
    (h : Module.finrank K (LinearMap.range (A + B)) =
      Module.finrank K (LinearMap.range A) + Module.finrank K (LinearMap.range B)) :
    LinearMap.range (A + B) = LinearMap.range A ⊔ LinearMap.range B := by
  apply Submodule.eq_of_le_of_finrank_le
  · rintro y ⟨x, rfl⟩
    exact Submodule.add_mem_sup (LinearMap.mem_range_self A x) (LinearMap.mem_range_self B x)
  · have hd := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range A) (LinearMap.range B)
    omega

lemma range_right_le_range_add_of_finrank_eq
    {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (A B : V →ₗ[K] W)
    (h : Module.finrank K (LinearMap.range (A + B)) =
      Module.finrank K (LinearMap.range A) + Module.finrank K (LinearMap.range B)) :
    LinearMap.range B ≤ LinearMap.range (A + B) := by
  rw [range_add_eq_sup_of_finrank_eq A B h]
  exact le_sup_right

lemma range_subtrahend_le_of_finrank_sub_add_eq
    {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (A Q : V →ₗ[K] W)
    (h : Module.finrank K (LinearMap.range (A - Q)) +
      Module.finrank K (LinearMap.range Q) = Module.finrank K (LinearMap.range A)) :
    LinearMap.range Q ≤ LinearMap.range A := by
  have he := range_right_le_range_add_of_finrank_eq (A - Q) Q
    (by rw [sub_add_cancel]; exact h.symm)
  rwa [sub_add_cancel] at he

lemma finrank_range_add_le_sum
    {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (A B : V →ₗ[K] W) :
    Module.finrank K (LinearMap.range (A + B)) ≤
      Module.finrank K (LinearMap.range A) + Module.finrank K (LinearMap.range B) := by
  have hle : LinearMap.range (A + B) ≤ LinearMap.range A ⊔ LinearMap.range B := by
    rintro y ⟨x, rfl⟩
    exact Submodule.add_mem_sup (LinearMap.mem_range_self A x) (LinearMap.mem_range_self B x)
  exact (Submodule.finrank_mono hle).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

lemma not_three_full_rank_drops_of_inf_eq_bot
    {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (D₁ D₂ D₃ Q : V →ₗ[K] W)
    (hq : Module.finrank K (LinearMap.range Q) ≠ 0)
    (hi : (LinearMap.range D₁ ⊓ LinearMap.range D₂) ⊓ LinearMap.range D₃ = ⊥) :
    ¬ ((Module.finrank K (LinearMap.range (D₁ - Q)) +
        Module.finrank K (LinearMap.range Q) = Module.finrank K (LinearMap.range D₁)) ∧
      (Module.finrank K (LinearMap.range (D₂ - Q)) +
        Module.finrank K (LinearMap.range Q) = Module.finrank K (LinearMap.range D₂)) ∧
      (Module.finrank K (LinearMap.range (D₃ - Q)) +
        Module.finrank K (LinearMap.range Q) = Module.finrank K (LinearMap.range D₃))) := by
  rintro ⟨h₁, h₂, h₃⟩
  have hle : LinearMap.range Q ≤
      (LinearMap.range D₁ ⊓ LinearMap.range D₂) ⊓ LinearMap.range D₃ :=
    le_inf (le_inf (range_subtrahend_le_of_finrank_sub_add_eq D₁ Q h₁)
      (range_subtrahend_le_of_finrank_sub_add_eq D₂ Q h₂))
      (range_subtrahend_le_of_finrank_sub_add_eq D₃ Q h₃)
  rw [hi] at hle
  have hd : Module.finrank K (LinearMap.range Q) ≤ 0 := by
    simpa using Submodule.finrank_mono hle
  exact hq (Nat.eq_zero_of_le_zero hd)

lemma full_rank_drop_of_even_of_rank_two
    {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (A Q : V →ₗ[K] W)
    (hq : Module.finrank K (LinearMap.range Q) = 2)
    (ha : Even (Module.finrank K (LinearMap.range A)))
    (hs : Even (Module.finrank K (LinearMap.range (A - Q))))
    (hlt : Module.finrank K (LinearMap.range (A - Q)) <
      Module.finrank K (LinearMap.range A)) :
    Module.finrank K (LinearMap.range (A - Q)) + 2 =
      Module.finrank K (LinearMap.range A) := by
  have ht := finrank_range_add_le_sum (A - Q) Q
  rw [sub_add_cancel, hq] at ht
  rcases ha with ⟨a, ha⟩
  rcases hs with ⟨s, hs⟩
  omega

lemma exists_nondecreasing_rank_of_three_inf_eq_bot
    {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (D : Fin 3 → V →ₗ[K] W) (Q : V →ₗ[K] W)
    (hq : Module.finrank K (LinearMap.range Q) = 2)
    (hi : (LinearMap.range (D 0) ⊓ LinearMap.range (D 1)) ⊓
      LinearMap.range (D 2) = ⊥)
    (hd : ∀ i, Even (Module.finrank K (LinearMap.range (D i))))
    (hs : ∀ i, Even (Module.finrank K (LinearMap.range (D i - Q)))) :
    ∃ i, Module.finrank K (LinearMap.range (D i)) ≤
      Module.finrank K (LinearMap.range (D i - Q)) := by
  by_contra hn
  push Not at hn
  have hf (i : Fin 3) := full_rank_drop_of_even_of_rank_two
    (D i) Q hq (hd i) (hs i) (hn i)
  exact not_three_full_rank_drops_of_inf_eq_bot (D 0) (D 1) (D 2) Q
    (by omega) hi (by simpa only [hq] using And.intro (hf 0) (And.intro (hf 1) (hf 2)))

def dyadicMass (n : ℕ) : ℚ := (1 / 2) ^ n

lemma dyadicMass_nonneg (n : ℕ) : 0 ≤ dyadicMass n := by
  unfold dyadicMass
  positivity

lemma dyadicMass_antitone : Antitone dyadicMass := by
  intro a b h
  exact pow_le_pow_of_le_one (by norm_num : (0 : ℚ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℚ) ≤ 1) h

lemma dyadicMass_quarter_gain (r w : ℕ) (hr : 1 ≤ r) (hw : w ≤ r + 1) :
    dyadicMass r ≤ dyadicMass w + 1 / 4 := by
  by_cases hr2 : 2 ≤ r
  · have h := dyadicMass_antitone hr2
    have hw0 := dyadicMass_nonneg w
    have hconst : dyadicMass 2 = (1 / 4 : ℚ) := by norm_num [dyadicMass]
    rw [hconst] at h
    linarith
  · have he : r = 1 := by omega
    subst r
    have h := dyadicMass_antitone (show w ≤ 2 by omega)
    norm_num [dyadicMass] at h ⊢
    linarith

lemma dyadicMass_four_bound
    (r₁ r₂ r₃ w₁ w₂ w₃ : ℕ)
    (hr₁ : 1 ≤ r₁) (hr₂ : 1 ≤ r₂) (hr₃ : 1 ≤ r₃)
    (hw₁ : w₁ ≤ r₁ + 1) (hw₂ : w₂ ≤ r₂ + 1) (hw₃ : w₃ ≤ r₃ + 1)
    (hstay : w₁ ≤ r₁ ∨ w₂ ≤ r₂ ∨ w₃ ≤ r₃) :
    1 / 2 + dyadicMass r₁ + dyadicMass r₂ + dyadicMass r₃ ≤
      1 + dyadicMass w₁ + dyadicMass w₂ + dyadicMass w₃ := by
  have h₁ := dyadicMass_quarter_gain r₁ w₁ hr₁ hw₁
  have h₂ := dyadicMass_quarter_gain r₂ w₂ hr₂ hw₂
  have h₃ := dyadicMass_quarter_gain r₃ w₃ hr₃ hw₃
  rcases hstay with h | h | h
  · have hh := dyadicMass_antitone h
    linarith
  · have hh := dyadicMass_antitone h
    linarith
  · have hh := dyadicMass_antitone h
    linarith

lemma rank_two_quartet_mass_bound
    {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (D : Fin 3 → V →ₗ[K] W) (Q : V →ₗ[K] W)
    (hq : Module.finrank K (LinearMap.range Q) = 2)
    (hi : (LinearMap.range (D 0) ⊓ LinearMap.range (D 1)) ⊓
      LinearMap.range (D 2) = ⊥)
    (hd : ∀ i, Even (Module.finrank K (LinearMap.range (D i))))
    (hs : ∀ i, Even (Module.finrank K (LinearMap.range (D i - Q))))
    (hp : ∀ i, 0 < Module.finrank K (LinearMap.range (D i - Q))) :
    dyadicMass (Module.finrank K (LinearMap.range Q) / 2) +
      ∑ i : Fin 3, dyadicMass (Module.finrank K (LinearMap.range (D i - Q)) / 2) ≤
      1 + ∑ i : Fin 3, dyadicMass (Module.finrank K (LinearMap.range (D i)) / 2) := by
  have hr (i : Fin 3) : 1 ≤ Module.finrank K (LinearMap.range (D i - Q)) / 2 := by
    obtain ⟨s, hs⟩ := hs i
    have := hp i
    omega
  have hw (i : Fin 3) : Module.finrank K (LinearMap.range (D i)) / 2 ≤
      Module.finrank K (LinearMap.range (D i - Q)) / 2 + 1 := by
    have ht := finrank_range_add_le_sum (D i - Q) Q
    rw [sub_add_cancel, hq] at ht
    omega
  obtain ⟨i, hstay⟩ := exists_nondecreasing_rank_of_three_inf_eq_bot D Q hq hi hd hs
  have hstay' : Module.finrank K (LinearMap.range (D 0)) / 2 ≤
        Module.finrank K (LinearMap.range (D 0 - Q)) / 2 ∨
      Module.finrank K (LinearMap.range (D 1)) / 2 ≤
        Module.finrank K (LinearMap.range (D 1 - Q)) / 2 ∨
      Module.finrank K (LinearMap.range (D 2)) / 2 ≤
        Module.finrank K (LinearMap.range (D 2 - Q)) / 2 := by
    fin_cases i
    · exact Or.inl (Nat.div_le_div_right hstay)
    · exact Or.inr (Or.inl (Nat.div_le_div_right hstay))
    · exact Or.inr (Or.inr (Nat.div_le_div_right hstay))
  have hbound := dyadicMass_four_bound
    (Module.finrank K (LinearMap.range (D 0 - Q)) / 2)
    (Module.finrank K (LinearMap.range (D 1 - Q)) / 2)
    (Module.finrank K (LinearMap.range (D 2 - Q)) / 2)
    (Module.finrank K (LinearMap.range (D 0)) / 2)
    (Module.finrank K (LinearMap.range (D 1)) / 2)
    (Module.finrank K (LinearMap.range (D 2)) / 2)
    (hr 0) (hr 1) (hr 2) (hw 0) (hw 1) (hw 2) hstay'
  have hqmass : dyadicMass (Module.finrank K (LinearMap.range Q) / 2) = 1 / 2 := by
    rw [hq]
    norm_num [dyadicMass]
  rw [hqmass]
  simpa [Fin.sum_univ_succ, add_assoc] using hbound

lemma f2_linear_add_self
    {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    (A : V →ₗ[ZMod 2] W) : A + A = 0 := by
  have htwo : (2 : ZMod 2) = 0 := by decide
  rw [← two_smul (ZMod 2), htwo, zero_smul]

lemma f2_linear_neg
    {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    (A : V →ₗ[ZMod 2] W) : -A = A := by
  exact neg_eq_iff_add_eq_zero.mpr (f2_linear_add_self A)

noncomputable def polarMass
    {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    (A : V →ₗ[ZMod 2] W) : ℚ :=
  dyadicMass (Module.finrank (ZMod 2) (LinearMap.range A) / 2)

noncomputable def planeMass
    {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    (A B Q : V →ₗ[ZMod 2] W) : ℚ :=
  polarMass Q + polarMass (Q + A) + polarMass (Q + B) + polarMass (Q + (A + B))

lemma planeMass_translate_left
    {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    (A B Q : V →ₗ[ZMod 2] W) : planeMass A B (Q + A) = planeMass A B Q := by
  have hqa : Q + A + A = Q := by rw [add_assoc, f2_linear_add_self, add_zero]
  have hqab : Q + A + (A + B) = Q + B := by
    rw [← add_assoc, hqa]
  simp only [planeMass, hqa, hqab, add_assoc]
  ring

lemma planeMass_translate_right
    {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    (A B Q : V →ₗ[ZMod 2] W) : planeMass A B (Q + B) = planeMass A B Q := by
  have hqb : Q + B + B = Q := by rw [add_assoc, f2_linear_add_self, add_zero]
  have hqba : Q + B + A = Q + (A + B) := by abel
  have hqbab : Q + B + (A + B) = Q + A := by
    calc
      _ = (Q + B + B) + A := by abel
      _ = Q + A := by rw [hqb]
  simp only [planeMass, hqb, hqba, hqbab]
  ring

lemma linear_eq_zero_of_range_finrank_zero
    {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (A : V →ₗ[K] W) (h : Module.finrank K (LinearMap.range A) = 0) : A = 0 := by
  have hz := (finrank_zero_iff_forall_zero).mp h
  ext x
  have hx := hz ⟨A x, LinearMap.mem_range_self A x⟩
  exact congrArg Subtype.val hx

lemma planeMass_zero
    {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    (A B : V →ₗ[ZMod 2] W) :
    planeMass A B 0 = 1 + polarMass A + polarMass B + polarMass (A + B) := by
  have hz : polarMass (0 : V →ₗ[ZMod 2] W) = 1 := by
    unfold polarMass
    rw [LinearMap.range_zero, finrank_bot]
    norm_num [dyadicMass]
  rw [planeMass, zero_add, zero_add, zero_add, hz]

lemma rank_two_planeMass_bound
    {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (A B Q : V →ₗ[ZMod 2] W)
    (hq : Module.finrank (ZMod 2) (LinearMap.range Q) = 2)
    (hi : (LinearMap.range A ⊓ LinearMap.range B) ⊓ LinearMap.range (A + B) = ⊥)
    (ha : Even (Module.finrank (ZMod 2) (LinearMap.range A)))
    (hb : Even (Module.finrank (ZMod 2) (LinearMap.range B)))
    (hab : Even (Module.finrank (ZMod 2) (LinearMap.range (A + B))))
    (hsa : Even (Module.finrank (ZMod 2) (LinearMap.range (Q + A))))
    (hsb : Even (Module.finrank (ZMod 2) (LinearMap.range (Q + B))))
    (hsab : Even (Module.finrank (ZMod 2) (LinearMap.range (Q + (A + B)))))
    (hpa : 0 < Module.finrank (ZMod 2) (LinearMap.range (Q + A)))
    (hpb : 0 < Module.finrank (ZMod 2) (LinearMap.range (Q + B)))
    (hpab : 0 < Module.finrank (ZMod 2) (LinearMap.range (Q + (A + B)))) :
    planeMass A B Q ≤ 1 + polarMass A + polarMass B + polarMass (A + B) := by
  let D : Fin 3 → V →ₗ[ZMod 2] W := ![A, B, A + B]
  have hd (i : Fin 3) : Even (Module.finrank (ZMod 2) (LinearMap.range (D i))) := by
    fin_cases i
    · exact ha
    · exact hb
    · exact hab
  have hsub (i : Fin 3) : D i - Q = Q + D i := by
    rw [sub_eq_add_neg, f2_linear_neg, add_comm]
  have hs (i : Fin 3) : Even (Module.finrank (ZMod 2) (LinearMap.range (D i - Q))) := by
    rw [hsub]
    fin_cases i
    · exact hsa
    · exact hsb
    · exact hsab
  have hp (i : Fin 3) : 0 < Module.finrank (ZMod 2) (LinearMap.range (D i - Q)) := by
    rw [hsub]
    fin_cases i
    · exact hpa
    · exact hpb
    · exact hpab
  have h := rank_two_quartet_mass_bound D Q hq hi hd hs hp
  simp only [Fin.sum_univ_succ] at h
  change polarMass Q + (polarMass (A - Q) + (polarMass (B - Q) +
    (polarMass ((A + B) - Q) + 0))) ≤
    1 + (polarMass A + (polarMass B + (polarMass (A + B) + 0))) at h
  have h1 : A - Q = Q + A := by rw [sub_eq_add_neg, f2_linear_neg, add_comm]
  have h2 : B - Q = Q + B := by rw [sub_eq_add_neg, f2_linear_neg, add_comm]
  have h3 : (A + B) - Q = Q + (A + B) := by rw [sub_eq_add_neg, f2_linear_neg, add_comm]
  rw [h1, h2, h3] at h
  unfold planeMass
  linarith

def planeAll
    {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    (P : (V →ₗ[ZMod 2] W) → Prop) (A B Q : V →ₗ[ZMod 2] W) : Prop :=
  P Q ∧ P (Q + A) ∧ P (Q + B) ∧ P (Q + (A + B))

lemma planeAll_translate_left
    {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    (P : (V →ₗ[ZMod 2] W) → Prop) (A B Q : V →ₗ[ZMod 2] W)
    (h : planeAll P A B Q) : planeAll P A B (Q + A) := by
  have hqa : Q + A + A = Q := by rw [add_assoc, f2_linear_add_self, add_zero]
  have hqab : Q + A + (A + B) = Q + B := by rw [← add_assoc, hqa]
  rcases h with ⟨h0, h1, h2, h3⟩
  exact ⟨h1, by rwa [hqa], by simpa only [add_assoc] using h3, by rwa [hqab]⟩

lemma planeAll_translate_right
    {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    (P : (V →ₗ[ZMod 2] W) → Prop) (A B Q : V →ₗ[ZMod 2] W)
    (h : planeAll P A B Q) : planeAll P A B (Q + B) := by
  have hqb : Q + B + B = Q := by rw [add_assoc, f2_linear_add_self, add_zero]
  have hqba : Q + B + A = Q + (A + B) := by abel
  have hqbab : Q + B + (A + B) = Q + A := by
    calc
      _ = (Q + B + B) + A := by abel
      _ = Q + A := by rw [hqb]
  rcases h with ⟨h0, h1, h2, h3⟩
  exact ⟨h2, by rwa [hqba], by rwa [hqb], by rwa [hqbab]⟩

lemma planeAll_translate_sum
    {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    (P : (V →ₗ[ZMod 2] W) → Prop) (A B Q : V →ₗ[ZMod 2] W)
    (h : planeAll P A B Q) : planeAll P A B (Q + (A + B)) := by
  rw [← add_assoc]
  exact planeAll_translate_right P A B (Q + A) (planeAll_translate_left P A B Q h)

lemma planeMass_translate_sum
    {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    (A B Q : V →ₗ[ZMod 2] W) : planeMass A B (Q + (A + B)) = planeMass A B Q := by
  rw [← add_assoc, planeMass_translate_right, planeMass_translate_left]

lemma translated_plane_mass_bound
    {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (A B Q : V →ₗ[ZMod 2] W)
    (hi : (LinearMap.range A ⊓ LinearMap.range B) ⊓ LinearMap.range (A + B) = ⊥)
    (ha : Even (Module.finrank (ZMod 2) (LinearMap.range A)))
    (hb : Even (Module.finrank (ZMod 2) (LinearMap.range B)))
    (hab : Even (Module.finrank (ZMod 2) (LinearMap.range (A + B))))
    (he : planeAll (fun X => Even (Module.finrank (ZMod 2) (LinearMap.range X))) A B Q) :
    planeMass A B Q ≤ 1 + polarMass A + polarMass B + polarMass (A + B) := by
  by_cases hz0 : Module.finrank (ZMod 2) (LinearMap.range Q) = 0
  · rw [linear_eq_zero_of_range_finrank_zero Q hz0, planeMass_zero]
  by_cases hz1 : Module.finrank (ZMod 2) (LinearMap.range (Q + A)) = 0
  · rw [← planeMass_translate_left A B Q,
      linear_eq_zero_of_range_finrank_zero (Q + A) hz1, planeMass_zero]
  by_cases hz2 : Module.finrank (ZMod 2) (LinearMap.range (Q + B)) = 0
  · rw [← planeMass_translate_right A B Q,
      linear_eq_zero_of_range_finrank_zero (Q + B) hz2, planeMass_zero]
  by_cases hz3 : Module.finrank (ZMod 2) (LinearMap.range (Q + (A + B))) = 0
  · rw [← planeMass_translate_sum A B Q,
      linear_eq_zero_of_range_finrank_zero (Q + (A + B)) hz3, planeMass_zero]
  have hp : planeAll (fun X => 0 < Module.finrank (ZMod 2) (LinearMap.range X)) A B Q :=
    ⟨Nat.pos_of_ne_zero hz0, Nat.pos_of_ne_zero hz1,
      Nat.pos_of_ne_zero hz2, Nat.pos_of_ne_zero hz3⟩
  have center (R : V →ₗ[ZMod 2] W)
      (hR : Module.finrank (ZMod 2) (LinearMap.range R) = 2)
      (heR : planeAll (fun X => Even (Module.finrank (ZMod 2) (LinearMap.range X))) A B R)
      (hpR : planeAll (fun X => 0 < Module.finrank (ZMod 2) (LinearMap.range X)) A B R) :
      planeMass A B R ≤ 1 + polarMass A + polarMass B + polarMass (A + B) :=
    rank_two_planeMass_bound A B R hR hi ha hb hab
      heR.2.1 heR.2.2.1 heR.2.2.2 hpR.2.1 hpR.2.2.1 hpR.2.2.2
  by_cases ht0 : Module.finrank (ZMod 2) (LinearMap.range Q) = 2
  · exact center Q ht0 he hp
  by_cases ht1 : Module.finrank (ZMod 2) (LinearMap.range (Q + A)) = 2
  · rw [← planeMass_translate_left A B Q]
    exact center (Q + A) ht1 (planeAll_translate_left _ A B Q he)
      (planeAll_translate_left _ A B Q hp)
  by_cases ht2 : Module.finrank (ZMod 2) (LinearMap.range (Q + B)) = 2
  · rw [← planeMass_translate_right A B Q]
    exact center (Q + B) ht2 (planeAll_translate_right _ A B Q he)
      (planeAll_translate_right _ A B Q hp)
  by_cases ht3 : Module.finrank (ZMod 2) (LinearMap.range (Q + (A + B))) = 2
  · rw [← planeMass_translate_sum A B Q]
    exact center (Q + (A + B)) ht3 (planeAll_translate_sum _ A B Q he)
      (planeAll_translate_sum _ A B Q hp)
  have four (n : ℕ) (heven : Even n) (hz : n ≠ 0) (ht : n ≠ 2) : 4 ≤ n := by
    obtain ⟨r, hr⟩ := heven
    omega
  have quarter (R : V →ₗ[ZMod 2] W)
      (hR : 4 ≤ Module.finrank (ZMod 2) (LinearMap.range R)) : polarMass R ≤ 1 / 4 := by
    calc
      polarMass R = dyadicMass (Module.finrank (ZMod 2) (LinearMap.range R) / 2) := rfl
      _ ≤ dyadicMass 2 := dyadicMass_antitone (by omega)
      _ = 1 / 4 := by norm_num [dyadicMass]
  have h0 := quarter Q (four _ he.1 hz0 ht0)
  have h1 := quarter (Q + A) (four _ he.2.1 hz1 ht1)
  have h2 := quarter (Q + B) (four _ he.2.2.1 hz2 ht2)
  have h3 := quarter (Q + (A + B)) (four _ he.2.2.2 hz3 ht3)
  have na : 0 ≤ polarMass A := dyadicMass_nonneg _
  have nb : 0 ≤ polarMass B := dyadicMass_nonneg _
  have nab : 0 ≤ polarMass (A + B) := dyadicMass_nonneg _
  unfold planeMass
  linarith

lemma translated_four_polar_mass_bound
    {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (A B Q : V →ₗ[ZMod 2] W)
    (hi : (LinearMap.range A ⊓ LinearMap.range B) ⊓ LinearMap.range (A + B) = ⊥)
    (ha : Even (Module.finrank (ZMod 2) (LinearMap.range A)))
    (hb : Even (Module.finrank (ZMod 2) (LinearMap.range B)))
    (hab : Even (Module.finrank (ZMod 2) (LinearMap.range (A + B))))
    (hq : Even (Module.finrank (ZMod 2) (LinearMap.range Q)))
    (hqa : Even (Module.finrank (ZMod 2) (LinearMap.range (Q + A))))
    (hqb : Even (Module.finrank (ZMod 2) (LinearMap.range (Q + B))))
    (hqab : Even (Module.finrank (ZMod 2) (LinearMap.range (Q + (A + B))))) :
    dyadicMass (Module.finrank (ZMod 2) (LinearMap.range Q) / 2) +
      dyadicMass (Module.finrank (ZMod 2) (LinearMap.range (Q + A)) / 2) +
      dyadicMass (Module.finrank (ZMod 2) (LinearMap.range (Q + B)) / 2) +
      dyadicMass (Module.finrank (ZMod 2) (LinearMap.range (Q + (A + B))) / 2) ≤
      1 + dyadicMass (Module.finrank (ZMod 2) (LinearMap.range A) / 2) +
      dyadicMass (Module.finrank (ZMod 2) (LinearMap.range B) / 2) +
      dyadicMass (Module.finrank (ZMod 2) (LinearMap.range (A + B)) / 2) := by
  exact translated_plane_mass_bound A B Q hi ha hb hab ⟨hq, hqa, hqb, hqab⟩

lemma dyadicMass_scaled (N r : ℕ) (hr : r ≤ N) :
    (2 : ℚ) ^ N * dyadicMass r = (2 : ℚ) ^ (N - r) := by
  have he : (2 : ℚ) ^ N = (2 : ℚ) ^ (N - r) * (2 : ℚ) ^ r := by
    rw [← pow_add, Nat.sub_add_cancel hr]
  unfold dyadicMass
  rw [he, mul_assoc, ← mul_pow]
  norm_num

lemma h2_polar_half_rank_le_finrank
    {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U]
    (P : U →ₗ[ZMod 2] Module.Dual (ZMod 2) U) :
    Module.finrank (ZMod 2) (LinearMap.range P) / 2 ≤ Module.finrank (ZMod 2) U := by
  have hn := LinearMap.finrank_range_add_finrank_ker P
  omega

lemma h2_sum_zmod2 {M : Type*} [AddCommMonoid M] (F : ZMod 2 → M) :
    (∑ s : ZMod 2, F s) = F 0 + F 1 := by
  have hu : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  rw [hu]
  simp

lemma h2_sum_zmod2_two {M : Type*} [AddCommMonoid M]
    (F : ZMod 2 → ZMod 2 → M) :
    (∑ s : ZMod 2, ∑ t : ZMod 2, F s t) =
      F 0 0 + F 1 0 + F 0 1 + F 1 1 := by
  rw [h2_sum_zmod2, h2_sum_zmod2, h2_sum_zmod2]
  ac_rfl

lemma h2_natAbs_four_le (a b c d : ℤ) (ca cb cc cd : ℕ)
    (ha : a.natAbs ≤ ca) (hb : b.natAbs ≤ cb)
    (hc : c.natAbs ≤ cc) (hd : d.natAbs ≤ cd) :
    (a + b + c + d).natAbs ≤ ca + cb + cc + cd := by
  have h₁ := Int.natAbs_add_le a b
  have h₂ := Int.natAbs_add_le (a + b) c
  have h₃ := Int.natAbs_add_le (a + b + c) d
  omega

lemma h2_four_fiber_int_natAbs_le
    {R : Type*} [Fintype R] (f : ZMod 2 → ZMod 2 → R → ℤ)
    (c00 c10 c01 c11 : ℕ)
    (h00 : (∑ x, f 0 0 x).natAbs ≤ c00)
    (h10 : (∑ x, f 1 0 x).natAbs ≤ c10)
    (h01 : (∑ x, f 0 1 x).natAbs ≤ c01)
    (h11 : (∑ x, f 1 1 x).natAbs ≤ c11) :
    (∑ s : ZMod 2, ∑ t : ZMod 2, ∑ x, f s t x).natAbs ≤ c00 + c10 + c01 + c11 := by
  rw [h2_sum_zmod2_two]
  exact h2_natAbs_four_le _ _ _ _ _ _ _ _ h00 h10 h01 h11

namespace GenericGauss

def chi (a : ZMod 2) : ℤ := if a = 0 then 1 else -1

lemma chi_add (a b : ZMod 2) : chi (a + b) = chi a * chi b := by
  fin_cases a <;> fin_cases b <;> rfl

lemma chi_le_one (a : ZMod 2) : chi a ≤ 1 := by
  fin_cases a <;> decide

lemma chi_four (a b c d : ZMod 2) :
    chi a * chi b = chi (c + d) * chi (a + b + c + d) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> rfl

lemma sum_chi_linear {U : Type*} [AddCommGroup U] [Module (ZMod 2) U] [Fintype U]
    (l : U →ₗ[ZMod 2] ZMod 2) :
    (∑ x : U, chi (l x)) = if l = 0 then (Fintype.card U : ℤ) else 0 := by
  classical
  split_ifs with hl
  · simp [hl, chi]
  · have hx : ∃ u : U, l u ≠ 0 := by
      by_contra! h
      apply hl
      ext u
      exact h u
    obtain ⟨u, hu⟩ := hx
    have hu1 : l u = 1 := by
      have hc : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
      exact (hc (l u)).resolve_left hu
    have ht := Equiv.sum_comp (Equiv.addRight u) (fun x : U => chi (l x))
    have hs : (∑ x : U, chi (l (x + u))) = -(∑ x : U, chi (l x)) := by
      simp only [map_add, chi_add, hu1]
      simp [chi, Finset.sum_neg_distrib]
    change (∑ x : U, chi (l (x + u))) = _ at ht
    rw [hs] at ht
    omega

lemma square_sum_eq {U : Type*} [AddCommGroup U] [Module (ZMod 2) U] [Fintype U]
    (q : U → ZMod 2) (P : U →ₗ[ZMod 2] Module.Dual (ZMod 2) U)
    (hpolar : ∀ x y, q (x + y) + q x + q y + q 0 = P x y) :
    (∑ x : U, chi (q x)) ^ 2 =
      (Fintype.card U : ℤ) * ∑ u : U, if P u = 0 then chi (q u + q 0) else 0 := by
  classical
  have heq : (∑ x : U, chi (q x)) ^ 2 =
      ∑ u : U, ∑ x : U, chi (q (u + x)) * chi (q x) := by
    rw [pow_two, Finset.sum_mul]
    have hr : ∀ x : U, (chi (q x) * ∑ y : U, chi (q y)) =
        ∑ u : U, chi (q (u + x)) * chi (q x) := by
      intro x
      have hx : (∑ u : U, chi (q (u + x))) = ∑ y : U, chi (q y) := by
        simpa using Equiv.sum_comp (Equiv.addRight x) (fun y : U => chi (q y))
      rw [← Finset.sum_mul, hx]
      ring
    simp_rw [hr]
    rw [Finset.sum_comm]
  rw [heq]
  have hi (u : U) : (∑ x : U, chi (q (u + x)) * chi (q x)) =
      (Fintype.card U : ℤ) * (if P u = 0 then chi (q u + q 0) else 0) := by
    have ht (x : U) : chi (q (u + x)) * chi (q x) =
        chi (q u + q 0) * chi (P u x) := by
      rw [chi_four (q (u+x)) (q x) (q u) (q 0)]
      congr 2
      rw [← hpolar u x]
      ring
    simp_rw [ht]
    rw [← Finset.mul_sum, sum_chi_linear]
    split_ifs <;> ring
  simp_rw [hi]
  rw [Finset.mul_sum]

lemma square_sum_le_card_mul_card_ker {U : Type*} [AddCommGroup U]
    [Module (ZMod 2) U] [Fintype U]
    (q : U → ZMod 2) (P : U →ₗ[ZMod 2] Module.Dual (ZMod 2) U)
    (hpolar : ∀ x y, q (x + y) + q x + q y + q 0 = P x y) :
    (∑ x : U, chi (q x)) ^ 2 ≤
      (Fintype.card U : ℤ) * Nat.card (LinearMap.ker P) := by
  classical
  let : Fintype (LinearMap.ker P) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  rw [square_sum_eq q P hpolar]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    (∑ u : U, if P u = 0 then chi (q u + q 0) else 0) ≤
        ∑ u : U, if P u = 0 then (1 : ℤ) else 0 := by
      apply Finset.sum_le_sum
      intro u _
      split_ifs
      · exact chi_le_one _
      · rfl
    _ = Fintype.card (LinearMap.ker P) := by
      rw [Fintype.card_subtype]
      simp [LinearMap.mem_ker]

lemma sum_chi_natAbs_le {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [Fintype U] [FiniteDimensional (ZMod 2) U]
    (q : U → ZMod 2) (P : U →ₗ[ZMod 2] Module.Dual (ZMod 2) U)
    (hpolar : ∀ x y, q (x + y) + q x + q y + q 0 = P x y) :
    (∑ x : U, chi (q x)).natAbs ≤
      2 ^ (Module.finrank (ZMod 2) U - Module.finrank (ZMod 2) (LinearMap.range P) / 2) := by
  classical
  have hc : Fintype.card U = 2 ^ Module.finrank (ZMod 2) U := by
    simpa using (Module.card_eq_pow_finrank (K := ZMod 2) (V := U))
  have hk : Nat.card (LinearMap.ker P) =
      2 ^ Module.finrank (ZMod 2) (LinearMap.ker P) := by
    simpa using (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := LinearMap.ker P))
  have hdim := P.finrank_range_add_finrank_ker
  have hb := square_sum_le_card_mul_card_ker q P hpolar
  rw [hc, hk] at hb
  push_cast at hb
  rw [← pow_add] at hb
  have hp : (2 : ℤ) ^ (Module.finrank (ZMod 2) U +
      Module.finrank (ZMod 2) (LinearMap.ker P)) ≤
      ((2 : ℤ) ^ (Module.finrank (ZMod 2) U -
        Module.finrank (ZMod 2) (LinearMap.range P) / 2)) ^ 2 := by
    rw [← pow_mul]
    gcongr <;> omega
  have hr := Int.natAbs_le_iff_sq_le.mpr (hb.trans hp)
  simpa using hr

lemma pow_two_eq_sq_even : ∀ N c : ℕ, c ^ 2 = 2 ^ N → Even N := by
  intro N
  induction N using Nat.strong_induction_on with
  | ind N ih =>
    intro c hc
    match N with
    | 0 => exact ⟨0, rfl⟩
    | 1 =>
      have : c ≤ 1 ∨ 2 ≤ c := by omega
      rcases this with h | h
      · have : c ^ 2 ≤ 1 := by nlinarith
        omega
      · have : 4 ≤ c ^ 2 := by nlinarith
        omega
    | N + 2 =>
      have h2dvd : 2 ∣ c ^ 2 := by
        rw [hc, pow_succ, pow_succ]
        exact ⟨2 ^ N * 2, by ring⟩
      have h2c : 2 ∣ c := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2dvd
      obtain ⟨c', rfl⟩ := h2c
      have hc' : c' ^ 2 = 2 ^ N := by
        have h1 : 4 * c' ^ 2 = 4 * 2 ^ N := by
          calc 4 * c' ^ 2 = (2 * c') ^ 2 := by ring
            _ = 2 ^ (N + 2) := hc
            _ = 4 * 2 ^ N := by ring
        omega
      obtain ⟨k, hk⟩ := ih N (by omega) c' hc'
      exact ⟨k + 1, by omega⟩

lemma even_rank_of_polar {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [Fintype U] [FiniteDimensional (ZMod 2) U]
    (q : U → ZMod 2) (P : U →ₗ[ZMod 2] Module.Dual (ZMod 2) U)
    (hpolar : ∀ x y, q (x + y) + q x + q y + q 0 = P x y) :
    Even (Module.finrank (ZMod 2) (LinearMap.range P)) := by
  classical
  have hself (a : ZMod 2) : a + a = 0 := by fin_cases a <;> rfl
  let K := LinearMap.ker P
  let lk : K →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun x => q x + q 0
      map_add' := by
        intro x y
        have hp := hpolar (x : U) (y : U)
        have hx : P x = 0 := x.property
        simp only [hx, LinearMap.zero_apply] at hp
        change q ((x : U) + (y : U)) + q 0 = (q x + q 0) + (q y + q 0)
        linear_combination hp - hself (q x) - hself (q y) - hself (q 0)
      map_smul' := by
        intro r x
        have hc : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
        rcases hc r with rfl | rfl <;> simp [hself] }
  let l := Subspace.dualLift K lk
  let q' : U → ZMod 2 := fun x => q x + l x
  have hp' : ∀ x y, q' (x + y) + q' x + q' y + q' 0 = P x y := by
    intro x y
    dsimp [q']
    simp only [map_add, map_zero, add_zero]
    linear_combination hpolar x y + hself (l x) + hself (l y)
  have hzero (u : U) (hu : P u = 0) : q' u + q' 0 = 0 := by
    have hlu : l u = q u + q 0 := by
      exact Subspace.dualLift_of_subtype (W := K) (φ := lk) ⟨u, hu⟩
    dsimp [q']
    rw [hlu, map_zero, add_zero]
    linear_combination hself (q u) + hself (q 0)
  let : Fintype K := Fintype.ofFinite _
  have hs : (∑ u : U, if P u = 0 then chi (q' u + q' 0) else 0) =
      (Nat.card K : ℤ) := by
    calc
      _ = ∑ u : U, if P u = 0 then (1 : ℤ) else 0 := by
        apply Finset.sum_congr rfl
        intro u _
        split_ifs with hu
        · rw [hzero u hu]
          rfl
        · rfl
      _ = _ := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
        simp [K, LinearMap.mem_ker]
  have hc : Fintype.card U = 2 ^ Module.finrank (ZMod 2) U := by
    simpa using (Module.card_eq_pow_finrank (K := ZMod 2) (V := U))
  have hk : Nat.card K = 2 ^ Module.finrank (ZMod 2) K := by
    simpa using (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := K))
  have heq := square_sum_eq q' P hp'
  rw [hs, hc, hk] at heq
  push_cast at heq
  rw [← pow_add] at heq
  have habs : (∑ x : U, chi (q' x)).natAbs ^ 2 =
      2 ^ (Module.finrank (ZMod 2) U + Module.finrank (ZMod 2) K) := by
    simpa using congrArg Int.natAbs heq
  obtain ⟨t, ht⟩ := pow_two_eq_sq_even _ _ habs
  have hdim := P.finrank_range_add_finrank_ker
  change Module.finrank (ZMod 2) (LinearMap.range P) + Module.finrank (ZMod 2) K =
    Module.finrank (ZMod 2) U at hdim
  exact ⟨t - Module.finrank (ZMod 2) K, by omega⟩

end GenericGauss

lemma h2_selector_quadratic_rational_cap
    {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [Fintype U] [FiniteDimensional (ZMod 2) U]
    (A B Q : U →ₗ[ZMod 2] Module.Dual (ZMod 2) U)
    (f : ZMod 2 → ZMod 2 → U → ZMod 2) (w₁ w₂ w₃ : ℕ)
    (hpolar : ∀ s t x y, f s t (x + y) + f s t x + f s t y + f s t 0 =
      (Q + s • A + t • B) x y)
    (hi : (LinearMap.range A ⊓ LinearMap.range B) ⊓ LinearMap.range (A + B) = ⊥)
    (ha : Module.finrank (ZMod 2) (LinearMap.range A) = 2 * w₁)
    (hb : Module.finrank (ZMod 2) (LinearMap.range B) = 2 * w₂)
    (hab : Module.finrank (ZMod 2) (LinearMap.range (A + B)) = 2 * w₃) :
    ((∑ s : ZMod 2, ∑ t : ZMod 2, ∑ x : U, GenericGauss.chi (f s t x)).natAbs : ℚ) ≤
      (2 : ℚ) ^ Module.finrank (ZMod 2) U *
        (1 + dyadicMass w₁ + dyadicMass w₂ + dyadicMass w₃) := by
  let N := Module.finrank (ZMod 2) U
  have hp00 (x y : U) : f 0 0 (x+y) + f 0 0 x + f 0 0 y + f 0 0 0 = Q x y := by
    simpa using hpolar 0 0 x y
  have hp10 (x y : U) : f 1 0 (x+y) + f 1 0 x + f 1 0 y + f 1 0 0 = (Q+A) x y := by
    simpa using hpolar 1 0 x y
  have hp01 (x y : U) : f 0 1 (x+y) + f 0 1 x + f 0 1 y + f 0 1 0 = (Q+B) x y := by
    simpa using hpolar 0 1 x y
  have hp11 (x y : U) : f 1 1 (x+y) + f 1 1 x + f 1 1 y + f 1 1 0 =
      (Q+(A+B)) x y := by
    simpa only [one_smul, add_assoc] using hpolar 1 1 x y
  have gauss (q : U → ZMod 2) (P : U →ₗ[ZMod 2] Module.Dual (ZMod 2) U)
      (hp : ∀ x y, q (x+y) + q x + q y + q 0 = P x y) :
      ((∑ x, GenericGauss.chi (q x)).natAbs : ℚ) ≤
        (2 : ℚ)^N * dyadicMass (Module.finrank (ZMod 2) (LinearMap.range P) / 2) := by
    rw [dyadicMass_scaled N _ (h2_polar_half_rank_le_finrank P)]
    exact_mod_cast GenericGauss.sum_chi_natAbs_le q P hp
  have g00 := gauss (f 0 0) Q hp00
  have g10 := gauss (f 1 0) (Q+A) hp10
  have g01 := gauss (f 0 1) (Q+B) hp01
  have g11 := gauss (f 1 1) (Q+(A+B)) hp11
  have hs := h2_four_fiber_int_natAbs_le (fun s t x => GenericGauss.chi (f s t x))
    _ _ _ _ (le_refl _) (le_refl _) (le_refl _) (le_refl _)
  have hsrat :
      ((∑ s : ZMod 2, ∑ t : ZMod 2, ∑ x : U, GenericGauss.chi (f s t x)).natAbs : ℚ) ≤
      ((∑ x, GenericGauss.chi (f 0 0 x)).natAbs : ℚ) +
      ((∑ x, GenericGauss.chi (f 1 0 x)).natAbs : ℚ) +
      ((∑ x, GenericGauss.chi (f 0 1 x)).natAbs : ℚ) +
      ((∑ x, GenericGauss.chi (f 1 1 x)).natAbs : ℚ) := by exact_mod_cast hs
  have hmass := translated_four_polar_mass_bound A B Q hi
    (show Even (Module.finrank (ZMod 2) (LinearMap.range A)) from ⟨w₁, by omega⟩)
    (show Even (Module.finrank (ZMod 2) (LinearMap.range B)) from ⟨w₂, by omega⟩)
    (show Even (Module.finrank (ZMod 2) (LinearMap.range (A+B))) from ⟨w₃, by omega⟩)
    (GenericGauss.even_rank_of_polar (f 0 0) Q hp00)
    (GenericGauss.even_rank_of_polar (f 1 0) (Q+A) hp10)
    (GenericGauss.even_rank_of_polar (f 0 1) (Q+B) hp01)
    (GenericGauss.even_rank_of_polar (f 1 1) (Q+(A+B)) hp11)
  rw [ha, hb, hab] at hmass
  have half (w : ℕ) : 2*w/2 = w := by omega
  rw [half, half, half] at hmass
  have hscaled := mul_le_mul_of_nonneg_left hmass (show 0 ≤ (2 : ℚ)^N by positivity)
  calc
    ((∑ s : ZMod 2, ∑ t : ZMod 2, ∑ x : U, GenericGauss.chi (f s t x)).natAbs : ℚ) ≤
        (2 : ℚ)^N * dyadicMass (Module.finrank (ZMod 2) (LinearMap.range Q) / 2) +
        (2 : ℚ)^N * dyadicMass (Module.finrank (ZMod 2) (LinearMap.range (Q+A)) / 2) +
        (2 : ℚ)^N * dyadicMass (Module.finrank (ZMod 2) (LinearMap.range (Q+B)) / 2) +
        (2 : ℚ)^N * dyadicMass (Module.finrank (ZMod 2) (LinearMap.range (Q+(A+B))) / 2) :=
      hsrat.trans (add_le_add (add_le_add (add_le_add g00 g10) g01) g11)
    _ = (2 : ℚ)^N *
        (dyadicMass (Module.finrank (ZMod 2) (LinearMap.range Q) / 2) +
        dyadicMass (Module.finrank (ZMod 2) (LinearMap.range (Q+A)) / 2) +
        dyadicMass (Module.finrank (ZMod 2) (LinearMap.range (Q+B)) / 2) +
        dyadicMass (Module.finrank (ZMod 2) (LinearMap.range (Q+(A+B))) / 2)) := by ring
    _ ≤ (2 : ℚ)^N * (1 + dyadicMass w₁ + dyadicMass w₂ + dyadicMass w₃) := hscaled

lemma h2_selector_quadratic_denominator_cap
    {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [Fintype U] [FiniteDimensional (ZMod 2) U]
    (A B Q : U →ₗ[ZMod 2] Module.Dual (ZMod 2) U)
    (f : ZMod 2 → ZMod 2 → U → ZMod 2) (w₁ w₂ w₃ D R : ℕ)
    (hpolar : ∀ s t x y, f s t (x + y) + f s t x + f s t y + f s t 0 =
      (Q + s • A + t • B) x y)
    (hi : (LinearMap.range A ⊓ LinearMap.range B) ⊓ LinearMap.range (A + B) = ⊥)
    (ha : Module.finrank (ZMod 2) (LinearMap.range A) = 2 * w₁)
    (hb : Module.finrank (ZMod 2) (LinearMap.range B) = 2 * w₂)
    (hab : Module.finrank (ZMod 2) (LinearMap.range (A + B)) = 2 * w₃)
    (hcap : (D : ℚ) * (1 + dyadicMass w₁ + dyadicMass w₂ + dyadicMass w₃) ≤
      4 * (R : ℚ)) :
    D * (∑ s : ZMod 2, ∑ t : ZMod 2, ∑ x : U, GenericGauss.chi (f s t x)).natAbs ≤
      R * (4 * Fintype.card U) := by
  have hbound := h2_selector_quadratic_rational_cap A B Q f w₁ w₂ w₃
    hpolar hi ha hb hab
  have hcard : Fintype.card U = 2 ^ Module.finrank (ZMod 2) U := by
    simpa using (Module.card_eq_pow_finrank (K := ZMod 2) (V := U))
  have hmul := mul_le_mul_of_nonneg_left hbound (show (0 : ℚ) ≤ D by positivity)
  have hcapmul := mul_le_mul_of_nonneg_left hcap
    (show 0 ≤ (2 : ℚ) ^ Module.finrank (ZMod 2) U by positivity)
  have hrat : (D : ℚ) *
      ((∑ s : ZMod 2, ∑ t : ZMod 2, ∑ x : U, GenericGauss.chi (f s t x)).natAbs : ℚ) ≤
      (R : ℚ) * (4 * (Fintype.card U : ℚ)) := by
    calc
      (D : ℚ) *
          ((∑ s : ZMod 2, ∑ t : ZMod 2, ∑ x : U, GenericGauss.chi (f s t x)).natAbs : ℚ) ≤
          (D : ℚ) * ((2 : ℚ) ^ Module.finrank (ZMod 2) U *
            (1 + dyadicMass w₁ + dyadicMass w₂ + dyadicMass w₃)) := hmul
      _ = (2 : ℚ) ^ Module.finrank (ZMod 2) U *
          ((D : ℚ) * (1 + dyadicMass w₁ + dyadicMass w₂ + dyadicMass w₃)) := by ring
      _ ≤ (2 : ℚ) ^ Module.finrank (ZMod 2) U * (4 * (R : ℚ)) := hcapmul
      _ = (R : ℚ) * (4 * (Fintype.card U : ℚ)) := by rw [hcard]; push_cast; ring
  exact_mod_cast hrat

lemma quadratic_affine_second_difference
    {U W : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [AddCommGroup W] [Module (ZMod 2) W]
    (q : U → ZMod 2) (c : ZMod 2) (l : U →ₗ[ZMod 2] ZMod 2)
    (B : U →ₗ[ZMod 2] U →ₗ[ZMod 2] ZMod 2)
    (hq : ∀ z, q z = c + l z + B z z)
    (L : W →ₗ[ZMod 2] U) (a : U) (x y : W) :
    q (a + L (x + y)) + q (a + L x) + q (a + L y) + q a =
      B (L x) (L y) + B (L y) (L x) := by
  simp only [hq, map_add, LinearMap.add_apply]
  ring_nf
  simp only [show (2 : ZMod 2) = 0 by decide, show (4 : ZMod 2) = 0 by decide,
    mul_zero, zero_add, add_zero]

lemma affine_linear_product_second_difference
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (u v : W →ₗ[ZMod 2] ZMod 2) (p r : ZMod 2) (x y : W) :
    (u (x + y) + p) * (v (x + y) + r) +
      (u x + p) * (v x + r) + (u y + p) * (v y + r) +
      (u 0 + p) * (v 0 + r) = u x * v y + u y * v x := by
  simp only [map_add, map_zero, zero_add]
  ring_nf
  simp only [show (2 : ZMod 2) = 0 by decide, show (4 : ZMod 2) = 0 by decide,
    mul_zero, zero_add, add_zero]

lemma affine_linear_pair_sum_second_difference
    {ι W : Type*} [Fintype ι] [AddCommGroup W] [Module (ZMod 2) W]
    (u v : ι → W →ₗ[ZMod 2] ZMod 2) (p r d : ι → ZMod 2) (x y : W) :
    let P := fun z => ∑ i, d i * (u i z + p i) * (v i z + r i)
    P (x + y) + P x + P y + P 0 =
      ∑ i, d i * (u i x * v i y + u i y * v i x) := by
  dsimp only
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = d i * ((u i (x + y) + p i) * (v i (x + y) + r i) +
        (u i x + p i) * (v i x + r i) + (u i y + p i) * (v i y + r i) +
        (u i 0 + p i) * (v i 0 + r i)) := by ring
    _ = _ := by rw [affine_linear_product_second_difference]

lemma selector_linear_forms_second_difference
    {ι U W : Type*} [Fintype ι]
    [AddCommGroup U] [Module (ZMod 2) U]
    [AddCommGroup W] [Module (ZMod 2) W]
    (q : U → ZMod 2) (q₀ : ZMod 2) (l : U →ₗ[ZMod 2] ZMod 2)
    (Bq : U →ₗ[ZMod 2] U →ₗ[ZMod 2] ZMod 2)
    (hq : ∀ z, q z = q₀ + l z + Bq z z)
    (L : W →ₗ[ZMod 2] U) (aq : U)
    (u v : ι → W →ₗ[ZMod 2] ZMod 2)
    (p r c a b : ι → ZMod 2) (s t η : ZMod 2) (x y : W) :
    let f := fun z => η + q (aq + L z) +
      ∑ i, (c i + s * a i + t * b i) * (u i z + p i) * (v i z + r i)
    f (x + y) + f x + f y + f 0 =
      Bq (L x) (L y) + Bq (L y) (L x) +
      (∑ i, c i * (u i x * v i y + u i y * v i x)) +
      s * (∑ i, a i * (u i x * v i y + u i y * v i x)) +
      t * (∑ i, b i * (u i x * v i y + u i y * v i x)) := by
  let d := fun i => c i + s * a i + t * b i
  let P := fun z => ∑ i, d i * (u i z + p i) * (v i z + r i)
  have hP := affine_linear_pair_sum_second_difference u v p r d x y
  change P (x + y) + P x + P y + P 0 =
    ∑ i, d i * (u i x * v i y + u i y * v i x) at hP
  have hQ := quadratic_affine_second_difference q q₀ l Bq hq L aq x y
  change (η + q (aq + L (x + y)) + P (x + y)) +
    (η + q (aq + L x) + P x) + (η + q (aq + L y) + P y) +
    (η + q (aq + L 0) + P 0) = _
  simp only [map_zero, add_zero]
  calc
    _ = (q (aq + L (x + y)) + q (aq + L x) + q (aq + L y) + q aq) +
        (P (x + y) + P x + P y + P 0) := by
      ring_nf
      simp only [show (4 : ZMod 2) = 0 by decide, mul_zero, zero_add]
    _ = (Bq (L x) (L y) + Bq (L y) (L x)) +
        ∑ i, d i * (u i x * v i y + u i y * v i x) := by rw [hQ, hP]
    _ = _ := by
      simp only [d, add_mul, Finset.sum_add_distrib, mul_assoc, Finset.mul_sum]
      ring

lemma h2_pair_forms_denominator_cap
    {ι U W : Type*} [Fintype ι]
    [AddCommGroup U] [Module (ZMod 2) U]
    [AddCommGroup W] [Module (ZMod 2) W]
    [Fintype W] [FiniteDimensional (ZMod 2) W]
    (q : U → ZMod 2) (q₀ : ZMod 2) (l : U →ₗ[ZMod 2] ZMod 2)
    (Bq : U →ₗ[ZMod 2] U →ₗ[ZMod 2] ZMod 2)
    (hq : ∀ z, q z = q₀ + l z + Bq z z)
    (L : W →ₗ[ZMod 2] U) (aq : ZMod 2 → ZMod 2 → U)
    (u v : ι → W →ₗ[ZMod 2] ZMod 2)
    (p r c a b : ι → ZMod 2) (η : ZMod 2 → ZMod 2 → ZMod 2)
    (P : (ι → ZMod 2) → W →ₗ[ZMod 2] Module.Dual (ZMod 2) W)
    (hP : ∀ d x y, P d x y = ∑ i, d i * (u i x * v i y + u i y * v i x))
    (w₁ w₂ w₃ D R : ℕ)
    (hi : (LinearMap.range (P a) ⊓ LinearMap.range (P b)) ⊓
      LinearMap.range (P a + P b) = ⊥)
    (ha : Module.finrank (ZMod 2) (LinearMap.range (P a)) = 2 * w₁)
    (hb : Module.finrank (ZMod 2) (LinearMap.range (P b)) = 2 * w₂)
    (hab : Module.finrank (ZMod 2) (LinearMap.range (P a + P b)) = 2 * w₃)
    (hcap : (D : ℚ) * (1 + dyadicMass w₁ + dyadicMass w₂ + dyadicMass w₃) ≤
      4 * (R : ℚ)) :
    D * (∑ s : ZMod 2, ∑ t : ZMod 2, ∑ x : W,
      GenericGauss.chi (η s t + q (aq s t + L x) +
        ∑ i, (c i + s * a i + t * b i) * (u i x + p i) * (v i x + r i))).natAbs ≤
      R * (4 * Fintype.card W) := by
  let Q : W →ₗ[ZMod 2] Module.Dual (ZMod 2) W :=
    (Bq.compl₂ L).comp L + (Bq.flip.compl₂ L).comp L + P c
  apply h2_selector_quadratic_denominator_cap (P a) (P b) Q
    (fun s t x => η s t + q (aq s t + L x) +
      ∑ i, (c i + s * a i + t * b i) * (u i x + p i) * (v i x + r i))
    w₁ w₂ w₃ D R ?_ hi ha hb hab hcap
  intro s t x y
  have hh := selector_linear_forms_second_difference q q₀ l Bq hq L (aq s t)
    u v p r c a b s t (η s t) x y
  simpa only [Q, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.compl₂_apply, LinearMap.flip_apply, LinearMap.smul_apply,
    smul_eq_mul, hP] using hh

namespace EmbeddedPolar

abbrev F := ZMod 2

def wordMap {I : Type*} (w : I → F) : (I → F) →ₗ[F] (I → F) where
  toFun x i := w i * x i
  map_add' x y := by ext i; simp [mul_add]
  map_smul' c x := by ext i; simp [smul_eq_mul, mul_left_comm]

lemma mem_range_wordMap {I : Type*} (w x : I → F) :
    x ∈ LinearMap.range (wordMap w) ↔ ∀ i, w i = 0 → x i = 0 := by
  constructor
  · rintro ⟨y, rfl⟩ i hi
    simp [wordMap, hi]
  · intro hx
    refine ⟨fun i => (w i)⁻¹ * x i, ?_⟩
    ext i
    by_cases hi : w i = 0
    · simp [wordMap, hi, hx i hi]
    · simp [wordMap, hi]

noncomputable def wordRangeEquiv {I : Type*} (w : I → F) :
    LinearMap.range (wordMap w) ≃ₗ[F] ({i : I // w i ≠ 0} → F) where
  toFun x i := x.val i.val
  invFun f := ⟨fun i => if hi : w i ≠ 0 then f ⟨i, hi⟩ else 0, by
    rw [mem_range_wordMap]
    intro i hi
    simp [hi]⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    by_cases hi : w i = 0
    · simp [hi, (mem_range_wordMap w x.val).mp x.property i hi]
    · simp [hi]
  right_inv f := by funext i; simp [i.property]
  map_add' x y := rfl
  map_smul' c x := rfl

lemma finrank_range_wordMap {I : Type*} [Fintype I] (w : I → F) :
    Module.finrank F (LinearMap.range (wordMap w)) =
      ((Finset.univ : Finset I).filter (fun i => w i ≠ 0)).card := by
  classical
  rw [(wordRangeEquiv w).finrank_eq, Module.finrank_fintype_fun_eq_card]
  exact Fintype.card_subtype _

def coordinateMap {I J : Type*} (pos : (I × Bool) ↪ J) (w : I → F) :
    (J → F) →ₗ[F] (I → F) × (I → F) where
  toFun x := (fun i => w i * x (pos (i, false)), fun i => w i * x (pos (i, true)))
  map_add' x y := by ext i <;> simp [mul_add]
  map_smul' c x := by ext i <;> simp [smul_eq_mul, mul_left_comm]

lemma mem_range_coordinateMap {I J : Type*} (pos : (I × Bool) ↪ J)
    (w : I → F) (x : (I → F) × (I → F)) :
    x ∈ LinearMap.range (coordinateMap pos w) ↔
      x.1 ∈ LinearMap.range (wordMap w) ∧ x.2 ∈ LinearMap.range (wordMap w) := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨⟨fun i => y (pos (i, false)), rfl⟩, ⟨fun i => y (pos (i, true)), rfl⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨Function.extend pos (fun p => if p.2 then b p.1 else a p.1) (fun _ => 0), ?_⟩
    apply Prod.ext
    · funext i
      change w i * Function.extend pos _ _ (pos (i, false)) = x.1 i
      rw [pos.injective.extend_apply]
      exact congrFun ha i
    · funext i
      change w i * Function.extend pos _ _ (pos (i, true)) = x.2 i
      rw [pos.injective.extend_apply]
      exact congrFun hb i

noncomputable def coordinateRangeEquiv {I J : Type*} (pos : (I × Bool) ↪ J) (w : I → F) :
    LinearMap.range (coordinateMap pos w) ≃ₗ[F]
      LinearMap.range (wordMap w) × LinearMap.range (wordMap w) where
  toFun x := (⟨x.val.1, ((mem_range_coordinateMap pos w x.val).mp x.property).1⟩,
    ⟨x.val.2, ((mem_range_coordinateMap pos w x.val).mp x.property).2⟩)
  invFun ab := ⟨(ab.1.val, ab.2.val),
    (mem_range_coordinateMap pos w _).mpr ⟨ab.1.property, ab.2.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma finrank_range_coordinateMap {I J : Type*} [Fintype I]
    (pos : (I × Bool) ↪ J) (w : I → F) :
    Module.finrank F (LinearMap.range (coordinateMap pos w)) =
      2 * ((Finset.univ : Finset I).filter (fun i => w i ≠ 0)).card := by
  rw [(coordinateRangeEquiv pos w).finrank_eq, Module.finrank_prod, finrank_range_wordMap]
  omega

def polar {I J : Type*} [Fintype I] (pos : (I × Bool) ↪ J) (w : I → F) :
    (J → F) →ₗ[F] Module.Dual F (J → F) :=
  LinearMap.mk₂ F
    (fun (x y : J → F) => ∑ i, w i *
      (x (pos (i, false)) * y (pos (i, true)) + y (pos (i, false)) * x (pos (i, true))))
    (by intro x y z; simp only [Pi.add_apply];
        simp only [add_mul, mul_add, Finset.sum_add_distrib]; ring)
    (by intro c x y
        change (∑ i, w i * ((c * x (pos (i, false))) * y (pos (i, true)) +
          y (pos (i, false)) * (c * x (pos (i, true))))) =
          c * ∑ i, w i * (x (pos (i, false)) * y (pos (i, true)) +
            y (pos (i, false)) * x (pos (i, true)))
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring)
    (by intro x y z; simp only [Pi.add_apply];
        simp only [add_mul, mul_add, Finset.sum_add_distrib]; ring)
    (by intro c x y
        change (∑ i, w i * (x (pos (i, false)) * (c * y (pos (i, true))) +
          (c * y (pos (i, false))) * x (pos (i, true)))) =
          c * ∑ i, w i * (x (pos (i, false)) * y (pos (i, true)) +
            y (pos (i, false)) * x (pos (i, true)))
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring)

lemma polar_apply {I J : Type*} [Fintype I] (pos : (I × Bool) ↪ J)
    (w : I → F) (x y : J → F) :
    polar pos w x y = ∑ i, w i *
      (x (pos (i, false)) * y (pos (i, true)) + y (pos (i, false)) * x (pos (i, true))) := rfl

lemma polar_add {I J : Type*} [Fintype I] (pos : (I × Bool) ↪ J) (a b : I → F) :
    polar pos (a + b) = polar pos a + polar pos b := by
  ext x y
  simp only [polar_apply, Pi.add_apply, add_mul, Finset.sum_add_distrib,
    LinearMap.add_apply]

lemma polar_eval_left {I J : Type*} [Fintype I] [DecidableEq J] (pos : (I × Bool) ↪ J)
    (w : I → F) (x : J → F) (i : I) :
    polar pos w x (Pi.single (pos (i, false)) 1) = w i * x (pos (i, true)) := by
  classical
  simp [polar_apply, Pi.single_apply, pos.injective.eq_iff, Finset.sum_ite_eq']

lemma polar_eval_right {I J : Type*} [Fintype I] [DecidableEq J] (pos : (I × Bool) ↪ J)
    (w : I → F) (x : J → F) (i : I) :
    polar pos w x (Pi.single (pos (i, true)) 1) = w i * x (pos (i, false)) := by
  classical
  simp [polar_apply, Pi.single_apply, pos.injective.eq_iff, Finset.sum_ite_eq']

lemma range_inactive_left {I J : Type*} [Fintype I] [DecidableEq J] (pos : (I × Bool) ↪ J)
    (w : I → F) (f : Module.Dual F (J → F))
    (hf : f ∈ LinearMap.range (polar pos w)) (i : I) (hi : w i = 0) :
    f (Pi.single (pos (i, false)) 1) = 0 := by
  rcases hf with ⟨x, rfl⟩
  rw [polar_eval_left, hi, zero_mul]

lemma range_inactive_right {I J : Type*} [Fintype I] [DecidableEq J] (pos : (I × Bool) ↪ J)
    (w : I → F) (f : Module.Dual F (J → F))
    (hf : f ∈ LinearMap.range (polar pos w)) (i : I) (hi : w i = 0) :
    f (Pi.single (pos (i, true)) 1) = 0 := by
  rcases hf with ⟨x, rfl⟩
  rw [polar_eval_right, hi, zero_mul]

lemma common_range_zero {I J : Type*} [Fintype I] (pos : (I × Bool) ↪ J)
    (a b : I → F) (f : Module.Dual F (J → F))
    (ha : f ∈ LinearMap.range (polar pos a))
    (hb : f ∈ LinearMap.range (polar pos b))
    (hab : f ∈ LinearMap.range (polar pos (a + b))) : f = 0 := by
  classical
  have hbits : ∀ x y : F, x = 0 ∨ y = 0 ∨ x + y = 0 := by decide
  have hleft : ∀ i : I, f (Pi.single (pos (i, false)) 1) = 0 := by
    intro i
    rcases hbits (a i) (b i) with h | h | h
    · exact range_inactive_left pos a f ha i h
    · exact range_inactive_left pos b f hb i h
    · exact range_inactive_left pos (a + b) f hab i h
  have hright : ∀ i : I, f (Pi.single (pos (i, true)) 1) = 0 := by
    intro i
    rcases hbits (a i) (b i) with h | h | h
    · exact range_inactive_right pos a f ha i h
    · exact range_inactive_right pos b f hb i h
    · exact range_inactive_right pos (a + b) f hab i h
  rcases ha with ⟨x, rfl⟩
  simp only [polar_eval_left] at hleft
  simp only [polar_eval_right] at hright
  ext y
  rw [polar_apply]
  apply Finset.sum_eq_zero
  intro i _
  calc
    a i * (x (pos (i, false)) * y (pos (i, true)) +
        y (pos (i, false)) * x (pos (i, true))) =
      (a i * x (pos (i, false))) * y (pos (i, true)) +
        (a i * x (pos (i, true))) * y (pos (i, false)) := by ring
    _ = 0 := by rw [hright i, hleft i]; ring

lemma triple_range_inf {I J : Type*} [Fintype I] (pos : (I × Bool) ↪ J) (a b : I → F) :
    LinearMap.range (polar pos a) ⊓ LinearMap.range (polar pos b) ⊓
      LinearMap.range (polar pos (a + b)) = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro f hf
  exact common_range_zero pos a b f hf.1.1 hf.1.2 hf.2

lemma ker_polar_eq {I J : Type*} [Fintype I] (pos : (I × Bool) ↪ J) (w : I → F) :
    LinearMap.ker (polar pos w) = LinearMap.ker (coordinateMap pos w) := by
  classical
  ext x
  simp only [LinearMap.mem_ker]
  constructor
  · intro hx
    apply Prod.ext
    · funext i
      have h := congrArg (fun f : Module.Dual F (J → F) =>
        f (Pi.single (pos (i, true)) 1)) hx
      change w i * x (pos (i, false)) = 0
      simpa only [polar_eval_right, LinearMap.zero_apply] using h
    · funext i
      have h := congrArg (fun f : Module.Dual F (J → F) =>
        f (Pi.single (pos (i, false)) 1)) hx
      change w i * x (pos (i, true)) = 0
      simpa only [polar_eval_left, LinearMap.zero_apply] using h
  · intro hx
    have hleft : ∀ i, w i * x (pos (i, false)) = 0 := by
      intro i
      exact congrArg (fun y : (I → F) × (I → F) => y.1 i) hx
    have hright : ∀ i, w i * x (pos (i, true)) = 0 := by
      intro i
      exact congrArg (fun y : (I → F) × (I → F) => y.2 i) hx
    ext y
    rw [polar_apply]
    apply Finset.sum_eq_zero
    intro i _
    calc
      w i * (x (pos (i, false)) * y (pos (i, true)) +
          y (pos (i, false)) * x (pos (i, true))) =
        (w i * x (pos (i, false))) * y (pos (i, true)) +
          (w i * x (pos (i, true))) * y (pos (i, false)) := by ring
      _ = 0 := by rw [hleft i, hright i]; ring

lemma finrank_range_polar {I J : Type*} [Fintype I] [Fintype J]
    (pos : (I × Bool) ↪ J) (w : I → F) :
    Module.finrank F (LinearMap.range (polar pos w)) =
      2 * ((Finset.univ : Finset I).filter (fun i => w i ≠ 0)).card := by
  have hp := LinearMap.finrank_range_add_finrank_ker (polar pos w)
  have hc := LinearMap.finrank_range_add_finrank_ker (coordinateMap pos w)
  rw [ker_polar_eq] at hp
  have he := Nat.add_right_cancel (hp.trans hc.symm)
  exact he.trans (finrank_range_coordinateMap pos w)

end EmbeddedPolar

def h2_wordWeight {I : Type*} [Fintype I] (w : I → ZMod 2) : ℕ :=
  ((Finset.univ : Finset I).filter (fun i => w i ≠ 0)).card

lemma h2_embedded_affine_quadratic_cap
    {I J U : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    [AddCommGroup U] [Module (ZMod 2) U]
    (pos : (I × Bool) ↪ J)
    (q : U → ZMod 2) (q₀ : ZMod 2) (l : U →ₗ[ZMod 2] ZMod 2)
    (Bq : U →ₗ[ZMod 2] U →ₗ[ZMod 2] ZMod 2)
    (hq : ∀ z, q z = q₀ + l z + Bq z z)
    (L : (J → ZMod 2) →ₗ[ZMod 2] U) (aq : ZMod 2 → ZMod 2 → U)
    (p r c a b : I → ZMod 2) (η : ZMod 2 → ZMod 2 → ZMod 2)
    (D R : ℕ)
    (hcap : (D : ℚ) * (1 + dyadicMass (h2_wordWeight a) +
      dyadicMass (h2_wordWeight b) + dyadicMass (h2_wordWeight (a + b))) ≤
      4 * (R : ℚ)) :
    D * (∑ s : ZMod 2, ∑ t : ZMod 2, ∑ x : J → ZMod 2,
      GenericGauss.chi (η s t + q (aq s t + L x) +
        ∑ i, (c i + s * a i + t * b i) *
          (x (pos (i, false)) + p i) * (x (pos (i, true)) + r i))).natAbs ≤
      R * (4 * Fintype.card (J → ZMod 2)) := by
  apply h2_pair_forms_denominator_cap q q₀ l Bq hq L aq
    (fun i => LinearMap.proj (pos (i, false)))
    (fun i => LinearMap.proj (pos (i, true)))
    p r c a b η (EmbeddedPolar.polar pos)
    (fun d x y => EmbeddedPolar.polar_apply pos d x y)
    (h2_wordWeight a) (h2_wordWeight b) (h2_wordWeight (a + b)) D R
    ?_ ?_ ?_ ?_ hcap
  · rw [← EmbeddedPolar.polar_add]
    exact EmbeddedPolar.triple_range_inf pos a b
  · exact EmbeddedPolar.finrank_range_polar pos a
  · exact EmbeddedPolar.finrank_range_polar pos b
  · rw [← EmbeddedPolar.polar_add]
    exact EmbeddedPolar.finrank_range_polar pos (a + b)

end PEqualNP.Outside.L_meta_32057_aux

namespace PEqualNP.Outside.L_meta_32057_aux

lemma embedded_pair_forms_denominator_cap
    {I J U : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    [AddCommGroup U] [Module (ZMod 2) U]
    (pos : (I × Bool) ↪ J)
    (q : U → ZMod 2) (q₀ : ZMod 2) (l : U →ₗ[ZMod 2] ZMod 2)
    (Bq : U →ₗ[ZMod 2] U →ₗ[ZMod 2] ZMod 2)
    (hq : ∀ z, q z = q₀ + l z + Bq z z)
    (L : (J → ZMod 2) →ₗ[ZMod 2] U) (aq : ZMod 2 → ZMod 2 → U)
    (p r c a b : I → ZMod 2) (η : ZMod 2 → ZMod 2 → ZMod 2)
    (D R : ℕ)
    (hcap : (D : ℚ) *
      (1 + dyadicMass ((Finset.univ.filter (fun i => a i ≠ 0)).card) +
        dyadicMass ((Finset.univ.filter (fun i => b i ≠ 0)).card) +
        dyadicMass ((Finset.univ.filter (fun i => a i + b i ≠ 0)).card)) ≤
      4 * (R : ℚ)) :
    D * (∑ s : ZMod 2, ∑ t : ZMod 2, ∑ x : J → ZMod 2,
      GenericGauss.chi (η s t + q (aq s t + L x) +
        ∑ i, (c i + s * a i + t * b i) *
          (x (pos (i, false)) + p i) * (x (pos (i, true)) + r i))).natAbs ≤
      R * (4 * Fintype.card (J → ZMod 2)) := by
  classical
  refine h2_pair_forms_denominator_cap q q₀ l Bq hq L aq
    (fun i => LinearMap.proj (pos (i, false)))
    (fun i => LinearMap.proj (pos (i, true)))
    p r c a b η (EmbeddedPolar.polar pos) ?_
    ((Finset.univ.filter (fun i => a i ≠ 0)).card)
    ((Finset.univ.filter (fun i => b i ≠ 0)).card)
    ((Finset.univ.filter (fun i => a i + b i ≠ 0)).card)
    D R ?_ ?_ ?_ ?_ hcap
  · intro d x y
    rfl
  · rw [← EmbeddedPolar.polar_add]
    exact EmbeddedPolar.triple_range_inf pos a b
  · exact EmbeddedPolar.finrank_range_polar pos a
  · exact EmbeddedPolar.finrank_range_polar pos b
  · rw [← EmbeddedPolar.polar_add]
    exact EmbeddedPolar.finrank_range_polar pos (a + b)


lemma finite_translate_average_bound
    {S T : Type*} [AddCommGroup S] [Fintype S] [Fintype T]
    (f : S → ℤ) (v : T → S) (B : ℕ)
    (h : ∀ s : S, (∑ t : T, f (s + v t)).natAbs ≤ B) :
    Fintype.card T * (∑ s : S, f s).natAbs ≤ Fintype.card S * B := by
  have hshift : ∀ t : T, (∑ s : S, f (s + v t)) = ∑ s : S, f s := by
    intro t
    exact Fintype.sum_equiv (Equiv.addRight (v t)) _ _ (fun _ => rfl)
  have hsum : (∑ s : S, ∑ t : T, f (s + v t)) =
      (Fintype.card T : ℤ) * (∑ s : S, f s) := by
    rw [Finset.sum_comm]
    simp_rw [hshift]
    simp
  have hh : ∀ s : S, |∑ t : T, f (s + v t)| ≤ (B : ℤ) := by
    intro s
    rw [← Int.natCast_natAbs]
    exact_mod_cast h s
  have havg : (Fintype.card T : ℤ) * |∑ s : S, f s| ≤ (Fintype.card S : ℤ) * B := by
    calc
      (Fintype.card T : ℤ) * |∑ s : S, f s| = |∑ s : S, ∑ t : T, f (s + v t)| := by
        have hcard : (0 : ℤ) ≤ (Fintype.card T : ℤ) := Nat.cast_nonneg _
        rw [hsum, abs_mul, abs_of_nonneg hcard]
      _ ≤ ∑ s : S, |∑ t : T, f (s + v t)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _s : S, (B : ℤ) := Finset.sum_le_sum (fun s _ => hh s)
      _ = (Fintype.card S : ℤ) * B := by simp
  simp only [← Int.natCast_natAbs] at havg
  exact_mod_cast havg

lemma finite_translate_average_scaled
    {S T : Type*} [AddCommGroup S] [Fintype S] [Fintype T]
    (f : S → ℤ) (v : T → S) (D B : ℕ)
    (h : ∀ s : S, D * (∑ t : T, f (s + v t)).natAbs ≤ B) :
    D * Fintype.card T * (∑ s : S, f s).natAbs ≤ Fintype.card S * B := by
  have hh := finite_translate_average_bound (fun s => (D : ℤ) * f s) v B (by
    intro s
    simpa only [← Finset.mul_sum, Int.natAbs_mul, Int.natAbs_natCast] using h s)
  simpa only [← Finset.mul_sum, Int.natAbs_mul, Int.natAbs_natCast,
    Nat.mul_left_comm, Nat.mul_assoc] using hh

lemma binary_plane_average_scaled
    {S : Type*} [AddCommGroup S] [Module (ZMod 2) S] [Fintype S]
    (f : S → ℤ) (a b : S) (D B : ℕ)
    (h : ∀ s : S,
      D * (∑ u : ZMod 2, ∑ v : ZMod 2, f (s + u • a + v • b)).natAbs ≤ 4 * B) :
    D * (∑ s : S, f s).natAbs ≤ Fintype.card S * B := by
  have hh := finite_translate_average_scaled f
    (fun p : ZMod 2 × ZMod 2 => p.1 • a + p.2 • b) D (4 * B) (by
      intro s
      simpa only [Fintype.sum_prod_type, add_assoc] using h s)
  have hcard : Fintype.card (ZMod 2 × ZMod 2) = 4 := by
    decide
  rw [hcard] at hh
  nlinarith

lemma two_nonzero_distinct_of_finrank
    {F T : Type*} [Field F] [AddCommGroup T] [Module F T] [Module.Finite F T]
    (hT : 2 ≤ Module.finrank F T) :
    ∃ a b : T, a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b := by
  let i : Fin (Module.finrank F T) := ⟨0, by omega⟩
  let j : Fin (Module.finrank F T) := ⟨1, by omega⟩
  refine ⟨Module.finBasis F T i, Module.finBasis F T j,
    (Module.finBasis F T).ne_zero i, (Module.finBasis F T).ne_zero j, ?_⟩
  intro h
  have hij := (Module.finBasis F T).injective h
  have hc := congrArg Fin.val hij
  change 0 = 1 at hc
  omega

lemma product_plane_average
    {U T W : Type*} [Fintype U] [Fintype T] [Fintype W]
    [AddCommGroup T] [Module (ZMod 2) T]
    (e : U ≃ T × W) (f : U → ℤ) (a b : T) (D R : ℕ)
    (h : ∀ s : T, D * (∑ u : ZMod 2, ∑ v : ZMod 2, ∑ w : W,
      f (e.symm (s + u • a + v • b, w))).natAbs ≤ R * (4 * Fintype.card W)) :
    D * (∑ x : U, f x).natAbs ≤ R * Fintype.card U := by
  have hh := binary_plane_average_scaled
    (fun s : T => ∑ w : W, f (e.symm (s, w))) a b D (R * Fintype.card W) (by
      intro s
      simpa only [Nat.mul_assoc, Nat.mul_left_comm] using h s)
  have hsum : (∑ s : T, ∑ w : W, f (e.symm (s, w))) = ∑ x : U, f x := by
    simpa only [Fintype.sum_prod_type] using e.symm.sum_comp f
  have hcard : Fintype.card U = Fintype.card T * Fintype.card W := by
    simpa only [Fintype.card_prod] using Fintype.card_congr e
  rw [hsum] at hh
  simpa only [hcard, Nat.mul_assoc, Nat.mul_left_comm] using hh


lemma terminal_flat_oracle_proved
    (S : Type) [AddCommGroup S] [Module F S] (D R : ℕ) :
    TerminalFlatOracle S D R := by
  classical
  intro U I J _ _ _ _ _ _ _ _ pos A h a L q hq hL hdim hcap hvertical
  let T := LinearMap.range ((LinearMap.fst F S (J → F)).comp L)
  let : Fintype T := Fintype.ofFinite T
  let e : U ≃ₗ[F] T × (J → F) := selectorDataEquiv L hL hvertical
  have ht : 2 ≤ Module.finrank F T :=
    selectorDataEquiv_surplus L hL hvertical 2 (by simpa using hdim)
  obtain ⟨u, v, hu, hv, huv⟩ := two_nonzero_distinct_of_finrank ht
  apply product_plane_average e.toEquiv
    (fun x => phaseSign (codePhase pos A h a L q x)) u v D R
  intro s
  obtain ⟨q₀, l, Bq, hq⟩ := hq
  let Ld : (J → F) →ₗ[F] U := e.symm.toLinearMap.comp (LinearMap.inr F T (J → F))
  let aq : F → F → U := fun t z => e.symm (s + t • u + z • v, 0)
  let p : I → F := fun i => a.2 (pos (i, false))
  let r : I → F := fun i => a.2 (pos (i, true))
  let c : I → F := fun i => A i (a.1 + s.val)
  let wa : I → F := fun i => A i u.val
  let wb : I → F := fun i => A i v.val
  let η : F → F → F := fun t z => h (a.1 + (s + t • u + z • v).val)
  have huna : u.val ≠ 0 := fun hzero => hu (Subtype.ext hzero)
  have hvna : v.val ≠ 0 := fun hzero => hv (Subtype.ext hzero)
  have huvne : u.val ≠ v.val := fun heq => huv (Subtype.ext heq)
  have hcap' := hcap u.val v.val u.property v.property huna hvna huvne
  have hwa : (Finset.univ.filter (fun i => wa i ≠ 0)).card =
      helper3_codeWeight A u.val := by
    unfold helper3_codeWeight
    apply congrArg Finset.card
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, wa]
  have hwb : (Finset.univ.filter (fun i => wb i ≠ 0)).card =
      helper3_codeWeight A v.val := by
    unfold helper3_codeWeight
    apply congrArg Finset.card
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, wb]
  have hwab : (Finset.univ.filter (fun i => wa i + wb i ≠ 0)).card =
      helper3_codeWeight A (u.val + v.val) := by
    unfold helper3_codeWeight
    apply congrArg Finset.card
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, wa, wb, map_add]
  have hh := embedded_pair_forms_denominator_cap pos q q₀ l Bq hq Ld aq
    p r c wa wb η D R (by
      simpa only [dyadicMass, hwa, hwb, hwab] using hcap')
  convert hh using 2
  apply congrArg Int.natAbs
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro w _
  have harg : aq t z + Ld w = e.symm (s + t • u + z • v, w) := by
    change e.symm (s + t • u + z • v, 0) + e.symm (0, w) = _
    rw [← map_add]
    simp
  rw [harg]
  unfold phaseSign GenericGauss.chi codePhase
  apply congrArg (fun f : F => if f = 0 then (1 : ℤ) else -1)
  have hc := selectorDataEquiv_affine_coordinates L hL hvertical a
    (s + t • u + z • v) w
  change a + L (e.symm (s + t • u + z • v, w)) = _ at hc
  change a + L (e.toEquiv.symm (s + t • u + z • v, w)) = _ at hc
  rw [hc]
  dsimp [η, c, wa, wb, p, r]
  simp only [map_add, map_smul, smul_eq_mul]
  apply congrArg₂ (· + ·)
  · exact add_comm _ _
  · apply Finset.sum_congr rfl
    intro i _
    ring

end PEqualNP.Outside.L_meta_32057_aux

namespace PEqualNP.Outside.L_meta_32057_aux

open scoped BigOperators

lemma full_vertical_coordinate_equiv
    {F U S D : Type*} [Field F]
    [AddCommGroup U] [Module F U]
    [AddCommGroup S] [Module F S]
    [AddCommGroup D] [Module F D]
    (L : U →ₗ[F] S × D) (hL : Function.Injective L)
    (hvertical : ∀ d : D, (0, d) ∈ LinearMap.range L) :
    ∃ e : U ≃ₗ[F] (LinearMap.range ((LinearMap.fst F S D).comp L)) × D,
      ∀ x, ((e x).1 : S) = (L x).1 ∧ (e x).2 = (L x).2 := by
  let p := (LinearMap.fst F S D).comp L
  let f : U →ₗ[F] (LinearMap.range p) × D :=
    p.rangeRestrict.prod ((LinearMap.snd F S D).comp L)
  have hinj : Function.Injective f := by
    intro x y h
    apply hL
    apply Prod.ext
    · exact congrArg (fun z : LinearMap.range p × D => (z.1 : S)) h
    · exact congrArg (fun z : LinearMap.range p × D => z.2) h
  have hsurj : Function.Surjective f := by
    rintro ⟨s, d⟩
    obtain ⟨x, hx⟩ := s.property
    obtain ⟨v, hv⟩ := hvertical (d - (L x).2)
    refine ⟨x + v, ?_⟩
    apply Prod.ext
    · apply Subtype.ext
      change p (x + v) = s.val
      rw [map_add, hx]
      have hz : p v = 0 := congrArg Prod.fst hv
      rw [hz, add_zero]
    · change (L (x + v)).2 = d
      rw [map_add, hv]
      simp
  refine ⟨LinearEquiv.ofBijective f ⟨hinj, hsurj⟩, ?_⟩
  intro x
  exact ⟨rfl, rfl⟩

lemma full_vertical_selector_shift
    {F U S D : Type*} [Field F]
    [AddCommGroup U] [Module F U]
    [AddCommGroup S] [Module F S]
    [AddCommGroup D] [Module F D]
    (L : U →ₗ[F] S × D) (a : S)
    (ha : a ∈ LinearMap.range ((LinearMap.fst F S D).comp L))
    (hvertical : ∀ d : D, (0, d) ∈ LinearMap.range L) :
    ∃ v : U, L v = (a, 0) := by
  obtain ⟨x, hx⟩ := ha
  obtain ⟨z, hz⟩ := hvertical (-(L x).2)
  refine ⟨x + z, ?_⟩
  rw [map_add, hz]
  apply Prod.ext
  · exact add_zero _ |>.trans hx
  · exact add_neg_cancel _

lemma exists_nonzero_selector_of_surplus
    {K U S J : Type*} [Field K]
    [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    [AddCommGroup S] [Module K S] [Fintype J]
    (L : U →ₗ[K] S × (J → K)) (hL : Function.Injective L)
    (hdim : Fintype.card J + 1 ≤ Module.finrank K U) :
    ∃ a : S, a ≠ 0 ∧ a ∈ LinearMap.range ((LinearMap.fst K S (J → K)).comp L) := by
  classical
  by_cases hz : ∀ x : U, (L x).1 = 0
  · let f : U →ₗ[K] (J → K) := (LinearMap.snd K S (J → K)).comp L
    have hf : Function.Injective f := by
      intro x y hxy
      apply hL
      exact Prod.ext (by rw [hz x, hz y]) hxy
    have hbound := LinearMap.finrank_le_finrank_of_injective hf
    rw [Module.finrank_fintype_fun_eq_card] at hbound
    omega
  · push Not at hz
    obtain ⟨x, hx⟩ := hz
    exact ⟨(L x).1, hx, ⟨x, rfl⟩⟩

lemma exists_nonzero_pure_selector_shift
    {K U S J : Type*} [Field K]
    [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    [AddCommGroup S] [Module K S] [Fintype J]
    (L : U →ₗ[K] S × (J → K)) (hL : Function.Injective L)
    (hdim : Fintype.card J + 1 ≤ Module.finrank K U)
    (hvertical : ∀ v : J → K, (0, v) ∈ LinearMap.range L) :
    ∃ (a : S) (v : U), a ≠ 0 ∧
      a ∈ LinearMap.range ((LinearMap.fst K S (J → K)).comp L) ∧ L v = (a, 0) := by
  obtain ⟨a, ha, hrange⟩ := exists_nonzero_selector_of_surplus L hL hdim
  obtain ⟨v, hv⟩ := full_vertical_selector_shift L a hrange hvertical
  exact ⟨a, v, ha, hrange, hv⟩

lemma terminal_coordinate_card
    {U T J : Type*} [AddCommGroup U] [Module F U]
    [AddCommGroup T] [Module F T] [Fintype U] [Fintype T] [Fintype J]
    (e : U ≃ₗ[F] T × (J → F)) :
    Fintype.card U = Fintype.card T * 2 ^ Fintype.card J := by
  classical
  simpa only [Fintype.card_prod, Fintype.card_fun, ZMod.card] using
    Fintype.card_congr e.toEquiv

lemma terminal_minWeight_card_bounds
    {U S I J : Type} [AddCommGroup U] [Module F U] [FiniteDimensional F U]
    [AddCommGroup S] [Module F S] [Fintype I] [DecidableEq I] [Fintype J]
    (pos : I × Bool ↪ J) (A : I → S →ₗ[F] F)
    (L : U →ₗ[F] S × (J → F)) (hL : Function.Injective L)
    (hdim : Fintype.card J + 1 ≤ Module.finrank F U) (d : ℕ)
    (hmin : minWeightCap A
      (LinearMap.range ((LinearMap.fst F S (J → F)).comp L)) d) :
    d ≤ Fintype.card I ∧ 2 * d ≤ Fintype.card J := by
  classical
  obtain ⟨a, ha, hrange⟩ := exists_nonzero_selector_of_surplus L hL hdim
  have hweight : helper3_codeWeight A a ≤ Fintype.card I := by
    unfold helper3_codeWeight
    exact Finset.card_le_univ _
  have hd := (hmin a hrange ha).trans hweight
  have hp : Fintype.card I * 2 ≤ Fintype.card J := by
    simpa only [Fintype.card_prod, Fintype.card_bool] using
      Fintype.card_le_of_injective pos pos.injective
  exact ⟨hd, by omega⟩

lemma pair_sum_to_normalized_line (d j T B : ℕ) (hd : 0 < d) (hdj : d ≤ j)
    (h : 2 * B ≤ T * 2 ^ j + 2 * T * 2 ^ (j - d)) :
    2 ^ d * B ≤ (2 ^ (d - 1) + 1) * (T * 2 ^ j) := by
  have hp : 2 ^ (d - 1) * 2 = 2 ^ d := by
    rw [← Nat.pow_succ]
    congr 1
    omega
  calc
    2 ^ d * B = 2 ^ (d - 1) * (2 * B) := by rw [← Nat.mul_assoc, hp]
    _ ≤ 2 ^ (d - 1) * (T * 2 ^ j + 2 * T * 2 ^ (j - d)) :=
      Nat.mul_le_mul_left _ h
    _ = (2 ^ (d - 1) + 1) * (T * 2 ^ j) := by
      have he : 2 ^ (d - 1) * (2 * T * 2 ^ (j - d)) = T * 2 ^ j := by
        calc
          2 ^ (d - 1) * (2 * T * 2 ^ (j - d)) = T * (2 ^ d * 2 ^ (j - d)) := by
            rw [← hp]
            ring
          _ = T * 2 ^ j := by rw [← Nat.pow_add, Nat.add_sub_of_le hdj]
      rw [Nat.mul_add, he]
      ring

lemma h8_cubic_difference_factor (u v w α β : ZMod 2) :
    (u + 1) * (v + α) * (w + β) + u * v * w =
      (v + α * (u + 1)) * (w + β * (u + 1)) := by
  revert u v w α β
  decide

def h8chi (x : ZMod 2) : ℤ := if x = 0 then 1 else -1

lemma h8chi_product_expansion (f u v : ZMod 2) :
    2 * h8chi (f + u * v) =
      h8chi f + h8chi (f + u) + h8chi (f + v) - h8chi (f + u + v) := by
  revert f u v
  decide

lemma h8_affine_add_shift {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (f : V →ᵃ[ZMod 2] ZMod 2) (x a : V) :
    f (x + a) = f x + f.linear a := by
  simpa only [vadd_eq_add, add_comm] using f.map_vadd x a

lemma h8_affine_product_derivative_first {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] (f g h : V →ᵃ[ZMod 2] ZMod 2) (a : V)
    (hf : f.linear a = 1) (x : V) :
    f (x + a) * g (x + a) * h (x + a) + f x * g x * h x =
      (g x + g.linear a * (f x + 1)) *
        (h x + h.linear a * (f x + 1)) := by
  rw [h8_affine_add_shift f, h8_affine_add_shift g, h8_affine_add_shift h, hf]
  exact h8_cubic_difference_factor (f x) (g x) (h x) (g.linear a) (h.linear a)

lemma h8_affine_product_derivative_factor {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] (f g h : V →ᵃ[ZMod 2] ZMod 2) (a : V) :
    ∃ p q : V →ᵃ[ZMod 2] ZMod 2, ∀ x,
      f (x + a) * g (x + a) * h (x + a) + f x * g x * h x = p x * q x := by
  have build : ∀ (f g h : V →ᵃ[ZMod 2] ZMod 2), f.linear a = 1 →
      ∃ p q : V →ᵃ[ZMod 2] ZMod 2, ∀ x,
        f (x + a) * g (x + a) * h (x + a) + f x * g x * h x = p x * q x := by
    intro f g h hf
    refine ⟨g + g.linear a • (f + AffineMap.const (ZMod 2) V 1),
      h + h.linear a • (f + AffineMap.const (ZMod 2) V 1), ?_⟩
    intro x
    exact h8_affine_product_derivative_first f g h a hf x
  have binary : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases binary (f.linear a) with hf | hf
  · rcases binary (g.linear a) with hg | hg
    · rcases binary (h.linear a) with hh | hh
      · refine ⟨0, 0, ?_⟩
        intro x
        rw [h8_affine_add_shift f, h8_affine_add_shift g, h8_affine_add_shift h,
          hf, hg, hh]
        change (f x + 0) * (g x + 0) * (h x + 0) + f x * g x * h x = 0 * 0
        have hz : ∀ z : ZMod 2, z + z = 0 := by decide
        simpa only [add_zero, mul_zero] using hz (f x * g x * h x)
      · obtain ⟨p, q, hpq⟩ := build h f g hh
        refine ⟨p, q, ?_⟩
        intro x
        convert hpq x using 1; ring
    · obtain ⟨p, q, hpq⟩ := build g f h hg
      refine ⟨p, q, ?_⟩
      intro x
      convert hpq x using 1; ring
  · exact build f g h hf



def sign8 (x : ZMod 2) : ℤ := if x = 0 then 1 else -1

lemma sign8_pair_pp (x y : ZMod 2) :
    sign8 x + sign8 y ≤ 1 + sign8 (x + y) := by
  fin_cases x <;> fin_cases y <;> decide

lemma sign8_pair_pm (x y : ZMod 2) :
    sign8 x - sign8 y ≤ 1 - sign8 (x + y) := by
  fin_cases x <;> fin_cases y <;> decide

lemma sign8_pair_mm (x y : ZMod 2) :
    -sign8 x - sign8 y ≤ 1 + sign8 (x + y) := by
  fin_cases x <;> fin_cases y <;> decide

lemma sign8_pair_sum {ι : Type*} [Fintype ι] (f g : ι → ZMod 2) :
    |∑ i, sign8 (f i)| + |∑ i, sign8 (g i)| ≤
      (Fintype.card ι : ℤ) + |∑ i, sign8 (f i + g i)| := by
  have hpp := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => sign8_pair_pp (f i) (g i))
  have hpm := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => sign8_pair_pm (f i) (g i))
  have hmp := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => sign8_pair_pm (g i) (f i))
  have hmm := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => sign8_pair_mm (f i) (g i))
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, add_comm (g _) (f _)]
    at hpp hpm hmp hmm
  have hc := le_abs_self (∑ i, sign8 (f i + g i))
  have hc' := neg_le_abs (∑ i, sign8 (f i + g i))
  rcases le_total 0 (∑ i, sign8 (f i)) with hf | hf <;>
    rcases le_total 0 (∑ i, sign8 (g i)) with hg | hg
  · rw [abs_of_nonneg hf, abs_of_nonneg hg]
    omega
  · rw [abs_of_nonneg hf, abs_of_nonpos hg]
    omega
  · rw [abs_of_nonpos hf, abs_of_nonneg hg]
    omega
  · rw [abs_of_nonpos hf, abs_of_nonpos hg]
    omega

lemma sign8_product_expansion (f u v : ZMod 2) :
    2 * sign8 (f + u * v) = sign8 f + sign8 (f + u) +
      sign8 (f + v) - sign8 (f + u + v) := by
  fin_cases f <;> fin_cases u <;> fin_cases v <;> decide

lemma sign8_product_sum_bound {ι : Type*} [Fintype ι]
    (f u v : ι → ZMod 2) (B : ℤ)
    (h0 : |∑ i, sign8 (f i)| ≤ B)
    (hu : |∑ i, sign8 (f i + u i)| ≤ B)
    (hv : |∑ i, sign8 (f i + v i)| ≤ B)
    (huv : |∑ i, sign8 (f i + u i + v i)| ≤ B) :
    |∑ i, sign8 (f i + u i * v i)| ≤ 2 * B := by
  have hs : 2 * (∑ i, sign8 (f i + u i * v i)) =
      (∑ i, sign8 (f i)) + (∑ i, sign8 (f i + u i)) +
      (∑ i, sign8 (f i + v i)) - (∑ i, sign8 (f i + u i + v i)) := by
    rw [Finset.mul_sum]
    simp_rw [sign8_product_expansion]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have habs := congrArg abs hs
  rw [abs_mul, show |(2 : ℤ)| = 2 by decide] at habs
  have h1 := abs_add_le (∑ i, sign8 (f i)) (∑ i, sign8 (f i + u i))
  have h2 := abs_add_le
    ((∑ i, sign8 (f i)) + (∑ i, sign8 (f i + u i)))
    (∑ i, sign8 (f i + v i))
  have h3 := abs_add_le
    ((∑ i, sign8 (f i)) + (∑ i, sign8 (f i + u i)) +
      (∑ i, sign8 (f i + v i)))
    (-(∑ i, sign8 (f i + u i + v i)))
  simp only [abs_neg, ← sub_eq_add_neg] at h3
  omega

lemma sign8_two_fibers_bound {ι : Type*} [Fintype ι]
    (f₀ f₁ f u v : ι → ZMod 2) (B : ℤ)
    (hderiv : ∀ i, f₀ i + f₁ i = f i + u i * v i)
    (h0 : |∑ i, sign8 (f i)| ≤ B)
    (hu : |∑ i, sign8 (f i + u i)| ≤ B)
    (hv : |∑ i, sign8 (f i + v i)| ≤ B)
    (huv : |∑ i, sign8 (f i + u i + v i)| ≤ B) :
    |∑ i, sign8 (f₀ i)| + |∑ i, sign8 (f₁ i)| ≤
      (Fintype.card ι : ℤ) + 2 * B := by
  have hp := sign8_pair_sum f₀ f₁
  simp_rw [hderiv] at hp
  have hb := sign8_product_sum_bound f u v B h0 hu hv huv
  omega

lemma sign8_shift_sum {V : Type*} [AddCommGroup V] [Fintype V]
    (f : V → ZMod 2) (a : V) :
    (∑ x, sign8 (f (x + a))) = ∑ x, sign8 (f x) := by
  exact Fintype.sum_equiv (Equiv.addRight a) _ _ (fun _ => rfl)

lemma sign8_shift_derivative_bound {V : Type*} [AddCommGroup V] [Fintype V]
    (f : V → ZMod 2) (a : V) (B : ℤ)
    (hderiv : |∑ x, sign8 (f x + f (x + a))| ≤ B) :
    2 * |∑ x, sign8 (f x)| ≤ (Fintype.card V : ℤ) + B := by
  have hp := sign8_pair_sum f (fun x => f (x + a))
  rw [sign8_shift_sum f a] at hp
  omega

lemma sign8_shift_product_bound {V : Type*} [AddCommGroup V] [Fintype V]
    (f Q u v : V → ZMod 2) (a : V) (B : ℤ)
    (hderiv : ∀ x, f x + f (x + a) = Q x + u x * v x)
    (h0 : |∑ x, sign8 (Q x)| ≤ B)
    (hu : |∑ x, sign8 (Q x + u x)| ≤ B)
    (hv : |∑ x, sign8 (Q x + v x)| ≤ B)
    (huv : |∑ x, sign8 (Q x + u x + v x)| ≤ B) :
    2 * |∑ x, sign8 (f x)| ≤ (Fintype.card V : ℤ) + 2 * B := by
  apply sign8_shift_derivative_bound f a (2 * B)
  simp_rw [hderiv]
  exact sign8_product_sum_bound Q u v B h0 hu hv huv
lemma h8_product_phase_bound {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Fintype V] (g : V → ZMod 2)
    (u v w : V →ᵃ[ZMod 2] ZMod 2) (a : V) (B : ℤ)
    (hWalsh : ∀ l : V →ᵃ[ZMod 2] ZMod 2,
      |∑ x, sign8 (g x + g (x + a) + l x)| ≤ B) :
    2 * |∑ x, sign8 (g x + u x * v x * w x)| ≤
      (Fintype.card V : ℤ) + 2 * B := by
  obtain ⟨p, q, hpq⟩ := h8_affine_product_derivative_factor u v w a
  apply sign8_shift_product_bound
    (fun x => g x + u x * v x * w x)
    (fun x => g x + g (x + a)) p q a B
  · intro x
    calc
      (g x + u x * v x * w x) +
          (g (x + a) + u (x + a) * v (x + a) * w (x + a)) =
        (g x + g (x + a)) +
          (u (x + a) * v (x + a) * w (x + a) + u x * v x * w x) := by ring
      _ = (g x + g (x + a)) + p x * q x := by rw [hpq x]
  · have hz := hWalsh 0
    change |∑ x, sign8 (g x + g (x + a) + 0)| ≤ B at hz
    simpa only [add_zero] using hz
  · exact hWalsh p
  · exact hWalsh q
  · have ha := hWalsh (p + q)
    change |∑ x, sign8 (g x + g (x + a) + (p x + q x))| ≤ B at ha
    simpa only [add_assoc] using ha


lemma h8_fiber_walsh_bound {S D V : Type*}
    [AddCommGroup S] [Module (ZMod 2) S] [Fintype S]
    [AddCommGroup D] [Module (ZMod 2) D] [Fintype D]
    [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    (e : V ≃ₗ[ZMod 2] S × D) (f : V → ZMod 2) (B : ℤ)
    (h : ∀ (s : S) (l : D →ᵃ[ZMod 2] ZMod 2),
      |∑ d, sign8 (f (e.symm (s, d)) + l d)| ≤ B)
    (l : V →ᵃ[ZMod 2] ZMod 2) :
    |∑ x, sign8 (f x + l x)| ≤ (Fintype.card S : ℤ) * B := by
  have hs (s : S) :
      |∑ d, sign8 (f (e.symm (s, d)) + l (e.symm (s, d)))| ≤ B := by
    let emb : D →ᵃ[ZMod 2] S × D :=
      (AffineMap.const (ZMod 2) D s).prod (AffineMap.id (ZMod 2) D)
    exact h s (l.comp (e.symm.toAffineMap.comp emb))
  have he : (∑ x, sign8 (f x + l x)) =
      ∑ s, ∑ d, sign8 (f (e.symm (s, d)) + l (e.symm (s, d))) := by
    rw [← Fintype.sum_prod_type']
    exact (e.symm.toEquiv.sum_comp (fun x => sign8 (f x + l x))).symm
  rw [he]
  calc
    |∑ s, ∑ d, sign8 (f (e.symm (s, d)) + l (e.symm (s, d)))| ≤
        ∑ s, |∑ d, sign8 (f (e.symm (s, d)) + l (e.symm (s, d)))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _s : S, B := Finset.sum_le_sum (fun s _ => hs s)
    _ = (Fintype.card S : ℤ) * B := by simp




lemma h8_affine_sum_apply {ι W : Type*} [Fintype ι]
    [AddCommGroup W] [Module (ZMod 2) W]
    (f : ι → W →ᵃ[ZMod 2] ZMod 2) (x : W) :
    (∑ i, f i) x = ∑ i, f i x := by
  let ev : (W →ᵃ[ZMod 2] ZMod 2) →+ ZMod 2 :=
    { toFun := fun l => l x
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  exact map_sum ev f Finset.univ

lemma h8_pair_shift_polynomial (s t u v p q : ZMod 2) :
    s * u * v + t * (u + p) * (v + q) =
      (s + t) * u * v + t * q * u + t * p * v + t * p * q := by
  ring

lemma h8_pair_family_derivative_affine {ι W : Type*} [Fintype ι]
    [AddCommGroup W] [Module (ZMod 2) W]
    (s t p q : ι → ZMod 2) (u v : ι → W →ᵃ[ZMod 2] ZMod 2) (z : ZMod 2) :
    ∃ l : W →ᵃ[ZMod 2] ZMod 2, ∀ x,
      z + ∑ i, (s i * u i x * v i x +
        t i * (u i x + p i) * (v i x + q i)) =
      (∑ i, (s i + t i) * u i x * v i x) + l x := by
  refine ⟨AffineMap.const (ZMod 2) W z + ∑ i,
    ((t i * q i) • u i + (t i * p i) • v i +
      AffineMap.const (ZMod 2) W (t i * p i * q i)), ?_⟩
  intro x
  simp only [h8_pair_shift_polynomial, Finset.sum_add_distrib]
  simp only [add_apply, h8_affine_sum_apply, smul_apply,
    AffineMap.const_apply, smul_eq_mul]
  ring

lemma h8_selector_derivative_affine {ι S W : Type*} [Fintype ι]
    [AddCommGroup S] [Module (ZMod 2) S]
    [AddCommGroup W] [Module (ZMod 2) W]
    (A : ι → S →ₗ[ZMod 2] ZMod 2) (h : S → ZMod 2)
    (s a : S) (p q : ι → ZMod 2)
    (u v : ι → W →ᵃ[ZMod 2] ZMod 2) :
    ∃ l : W →ᵃ[ZMod 2] ZMod 2, ∀ x,
      (h s + ∑ i, A i s * u i x * v i x) +
        (h (s + a) + ∑ i, A i (s + a) *
          (u i x + p i) * (v i x + q i)) =
      (∑ i, A i a * u i x * v i x) + l x := by
  obtain ⟨l, hl⟩ := h8_pair_family_derivative_affine
    (fun i => A i s) (fun i => A i (s + a)) p q u v (h s + h (s + a))
  refine ⟨l, ?_⟩
  intro x
  have hz (i : ι) : A i s + A i (s + a) = A i a := by
    rw [map_add, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  have hx := hl x
  simp only [hz, Finset.sum_add_distrib] at hx
  convert hx using 1; ring

lemma h8_selector_derivative_walsh_bound {ι S W : Type*} [Fintype ι]
    [AddCommGroup S] [Module (ZMod 2) S]
    [AddCommGroup W] [Module (ZMod 2) W] [Fintype W]
    (A : ι → S →ₗ[ZMod 2] ZMod 2) (h : S → ZMod 2)
    (s a : S) (p q : ι → ZMod 2)
    (u v : ι → W →ᵃ[ZMod 2] ZMod 2) (B : ℤ)
    (hcore : ∀ l : W →ᵃ[ZMod 2] ZMod 2,
      |∑ x, sign8 ((∑ i, A i a * u i x * v i x) + l x)| ≤ B)
    (l : W →ᵃ[ZMod 2] ZMod 2) :
    |∑ x, sign8 ((h s + ∑ i, A i s * u i x * v i x) +
        (h (s + a) + ∑ i, A i (s + a) *
          (u i x + p i) * (v i x + q i)) + l x)| ≤ B := by
  obtain ⟨r, hr⟩ := h8_selector_derivative_affine A h s a p q u v
  convert hcore (r + l) using 1
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  congr 1
  rw [hr x]
  change (∑ i, A i a * u i x * v i x) + r x + l x =
    (∑ i, A i a * u i x * v i x) + (r x + l x)
  ring

lemma h8_affine_apply_linear {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (f : W →ᵃ[ZMod 2] ZMod 2) (x : W) :
    f x = f.linear x + f 0 := by
  simpa only [vadd_eq_add, add_zero] using f.map_vadd 0 x

lemma h8_affine_pairs_remainder {ι W : Type*} [Fintype ι]
    [AddCommGroup W] [Module (ZMod 2) W]
    (u v : ι → W →ᵃ[ZMod 2] ZMod 2) :
    ∃ l : W →ᵃ[ZMod 2] ZMod 2, ∀ x,
      (∑ i, u i x * v i x) =
        (∑ i, (u i).linear x * (v i).linear x) + l x := by
  obtain ⟨l, hl⟩ := h8_pair_family_derivative_affine
    (fun _ : ι => 0) (fun _ : ι => 1)
    (fun i => u i 0) (fun i => v i 0)
    (fun i => (u i).linear.toAffineMap) (fun i => (v i).linear.toAffineMap) 0
  refine ⟨l, ?_⟩
  intro x
  have hx := hl x
  change 0 + (∑ i, (0 * (u i).linear x * (v i).linear x +
      1 * ((u i).linear x + u i 0) * ((v i).linear x + v i 0))) =
    (∑ i, (0 + 1) * (u i).linear x * (v i).linear x) + l x at hx
  simpa only [zero_mul, zero_add, one_mul, ← h8_affine_apply_linear] using hx

lemma h8_active_pair_sum {ι : Type*} [Fintype ι]
    (c u v : ι → ZMod 2) :
    (∑ i, c i * u i * v i) =
      ∑ i : {i : ι // c i ≠ 0}, u i.val * v i.val := by
  classical
  have hc (i : ι) : c i * u i * v i =
      if c i ≠ 0 then u i * v i else 0 := by
    have scalar : ∀ c u v : ZMod 2,
        c * u * v = if c ≠ 0 then u * v else 0 := by decide
    exact scalar _ _ _
  simp_rw [hc]
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) (fun i => u i * v i)

lemma h8_q2_derivative_affine {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V]
    (q : V → ZMod 2)
    (hq : ∃ (c : ZMod 2) (l : V →ₗ[ZMod 2] ZMod 2)
      (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2), ∀ x, q x = c + l x + B x x)
    (a : V) :
    ∃ f : V →ᵃ[ZMod 2] ZMod 2, ∀ x, q (x + a) + q x = f x := by
  obtain ⟨c, l, B, hq⟩ := hq
  refine ⟨(B.flip a + B a).toAffineMap +
    AffineMap.const (ZMod 2) V (l a + B a a), ?_⟩
  intro x
  change q (x + a) + q x = (B x a + B a x) + (l a + B a a)
  rw [hq (x + a), hq x]
  simp only [map_add, LinearMap.add_apply]
  have hz (z : ZMod 2) : z + z = 0 := CharTwo.add_self_eq_zero z
  calc
    c + (l x + l a) + (B x x + B a x + (B x a + B a a)) + (c + l x + B x x) =
      (c + c) + (l x + l x) + (B x x + B x x) + (B x a + B a x) + (l a + B a a) := by ring
    _ = _ := by simp only [hz, zero_add]

lemma h8_q2_product_phase_bound {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    (g q : V → ZMod 2)
    (hq : ∃ (c : ZMod 2) (l : V →ₗ[ZMod 2] ZMod 2)
      (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2), ∀ x, q x = c + l x + B x x)
    (u v w : V →ᵃ[ZMod 2] ZMod 2) (a : V) (B : ℤ)
    (hWalsh : ∀ l : V →ᵃ[ZMod 2] ZMod 2,
      |∑ x, sign8 (g x + g (x + a) + l x)| ≤ B) :
    2 * |∑ x, sign8 (g x + q x + u x * v x * w x)| ≤
      (Fintype.card V : ℤ) + 2 * B := by
  obtain ⟨Q, hQ⟩ := h8_q2_derivative_affine q hq a
  apply h8_product_phase_bound (fun x => g x + q x) u v w a B
  intro l
  convert hWalsh (Q + l) using 1
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  congr 1
  change g x + q x + (g (x + a) + q (x + a)) + l x =
    g x + g (x + a) + (Q x + l x)
  rw [← hQ x]
  ring

lemma h8_q2_product_fiber_natAbs_bound {V S D : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    [AddCommGroup S] [Module (ZMod 2) S] [Fintype S]
    [AddCommGroup D] [Module (ZMod 2) D] [Fintype D]
    (e : V ≃ₗ[ZMod 2] S × D) (g q : V → ZMod 2)
    (hq : ∃ (c : ZMod 2) (l : V →ₗ[ZMod 2] ZMod 2)
      (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2), ∀ x, q x = c + l x + B x x)
    (u v w : V →ᵃ[ZMod 2] ZMod 2) (a : V) (B : ℕ)
    (hWalsh : ∀ (s : S) (l : D →ᵃ[ZMod 2] ZMod 2),
      |∑ d, sign8 (g (e.symm (s, d)) + g (e.symm (s, d) + a) + l d)| ≤ (B : ℤ)) :
    2 * (∑ x, sign8 (g x + q x + u x * v x * w x)).natAbs ≤
      Fintype.card V + 2 * Fintype.card S * B := by
  have h := h8_q2_product_phase_bound g q hq u v w a
    ((Fintype.card S : ℤ) * B)
    (h8_fiber_walsh_bound e (fun x => g x + g (x + a)) (B : ℤ) hWalsh)
  simp only [← Int.natCast_natAbs] at h
  have h' : (2 : ℤ) * (∑ x, sign8 (g x + q x + u x * v x * w x)).natAbs ≤
      (Fintype.card V : ℤ) + 2 * (Fintype.card S : ℤ) * (B : ℤ) := by
    simpa only [mul_assoc] using h
  exact_mod_cast h'

lemma h8_selector_q2_product_fiber_natAbs_bound {ι V S T D : Type*}
    [Fintype ι] [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    [AddCommGroup S] [Module (ZMod 2) S]
    [AddCommGroup T] [Module (ZMod 2) T] [Fintype T]
    [AddCommGroup D] [Module (ZMod 2) D] [Fintype D]
    (e : V ≃ₗ[ZMod 2] T × D)
    (sel : V →ᵃ[ZMod 2] S)
    (c : T → S) (hsel : ∀ t d, sel (e.symm (t, d)) = c t)
    (A : ι → S →ₗ[ZMod 2] ZMod 2) (h : S → ZMod 2)
    (u v : ι → V →ᵃ[ZMod 2] ZMod 2)
    (q : V → ZMod 2)
    (hq : ∃ (c : ZMod 2) (l : V →ₗ[ZMod 2] ZMod 2)
      (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2), ∀ x, q x = c + l x + B x x)
    (f₁ f₂ f₃ : V →ᵃ[ZMod 2] ZMod 2)
    (a : V) (B : ℕ)
    (hcore : ∀ (t : T) (l : D →ᵃ[ZMod 2] ZMod 2),
      |∑ d, sign8 ((∑ i, A i (sel.linear a) *
        u i (e.symm (t, d)) * v i (e.symm (t, d))) + l d)| ≤ (B : ℤ)) :
    2 * (∑ x, sign8 ((h (sel x) + ∑ i, A i (sel x) * u i x * v i x) +
      q x + f₁ x * f₂ x * f₃ x)).natAbs ≤
      Fintype.card V + 2 * Fintype.card T * B := by
  let g : V → ZMod 2 :=
    fun x => h (sel x) + ∑ i, A i (sel x) * u i x * v i x
  apply h8_q2_product_fiber_natAbs_bound e g q hq f₁ f₂ f₃ a B
  intro t l
  let emb : D →ᵃ[ZMod 2] V :=
    e.symm.toAffineMap.comp
      ((AffineMap.const (ZMod 2) D t).prod (AffineMap.id (ZMod 2) D))
  have hb := h8_selector_derivative_walsh_bound A h (c t) (sel.linear a)
    (fun i => (u i).linear a) (fun i => (v i).linear a)
    (fun i => (u i).comp emb) (fun i => (v i).comp emb) (B : ℤ)
    (hcore t) l
  convert hb using 1
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  congr 1
  dsimp only [g]
  have hsa : sel (e.symm (t, d) + a) = c t + sel.linear a := by
    simpa only [vadd_eq_add, hsel, add_comm] using sel.map_vadd (e.symm (t, d)) a
  simp only [h8_affine_add_shift, hsa, hsel]
  rfl

lemma terminal_line_of_embedded_walsh
    (hpair : ∀ (I J : Type) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
      (pos : I × Bool ↪ J) (w : I → F) (p : J → F) (l : (J → F) →ᵃ[F] F),
      |∑ z : J → F, sign8 ((∑ i : I, w i * (p (pos (i, false)) + z (pos (i, false))) *
        (p (pos (i, true)) + z (pos (i, true)))) + l z)| ≤
        (2 : ℤ) ^ (Fintype.card J - (Finset.univ.filter fun i => w i ≠ 0).card))
    (S : Type) [AddCommGroup S] [Module F S] (d : ℕ) (hd : 0 < d) :
    TerminalLineOracle S d (2 ^ d) (2 ^ (d - 1) + 1) := by
  classical
  intro U I J _ _ _ _ _ _ _ _ pos A h a L q hq hL hdim hmin hvertical
  obtain ⟨s, v0, hs, hsrange, hv0⟩ :=
    exists_nonzero_pure_selector_shift L hL hdim hvertical
  have hweight : d ≤ helper3_codeWeight A s := hmin s hsrange hs
  have hdj : d ≤ Fintype.card J := by
    have hb := terminal_minWeight_card_bounds pos A L hL hdim d hmin
    omega
  let T := LinearMap.range ((LinearMap.fst F S (J → F)).comp L)
  let : Fintype T := Fintype.ofFinite T
  obtain ⟨e, he⟩ := full_vertical_coordinate_equiv L hL hvertical
  have hesymm (t : T) (z : J → F) : L (e.symm (t, z)) = ((t : S), z) := by
    have hh := he (e.symm (t, z))
    simp only [e.apply_symm_apply] at hh
    exact Prod.ext hh.1.symm hh.2.symm
  let sel : U →ᵃ[F] S :=
    ((LinearMap.fst F S (J → F)).comp L).toAffineMap + AffineMap.const F U a.1
  let u : I → U →ᵃ[F] F := fun i =>
    ((LinearMap.proj (pos (i, false))).comp ((LinearMap.snd F S (J → F)).comp L)).toAffineMap +
      AffineMap.const F U (a.2 (pos (i, false)))
  let v : I → U →ᵃ[F] F := fun i =>
    ((LinearMap.proj (pos (i, true))).comp ((LinearMap.snd F S (J → F)).comp L)).toAffineMap +
      AffineMap.const F U (a.2 (pos (i, true)))
  have hsel (t : T) (z : J → F) : sel (e.symm (t, z)) = a.1 + (t : S) := by
    change (L (e.symm (t, z))).1 + a.1 = _
    rw [hesymm]
    exact add_comm _ _
  have hselshift : sel.linear v0 = s := by
    simp [sel, hv0]
  have hu (i : I) (t : T) (z : J → F) :
      u i (e.symm (t, z)) = a.2 (pos (i, false)) + z (pos (i, false)) := by
    change (L (e.symm (t, z))).2 (pos (i, false)) + a.2 (pos (i, false)) = _
    rw [hesymm]
    exact add_comm _ _
  have hv (i : I) (t : T) (z : J → F) :
      v i (e.symm (t, z)) = a.2 (pos (i, true)) + z (pos (i, true)) := by
    change (L (e.symm (t, z))).2 (pos (i, true)) + a.2 (pos (i, true)) = _
    rw [hesymm]
    exact add_comm _ _
  obtain ⟨q0, f1, f2, f3, hq0, hf1, hf2, hf3, hq⟩ := hq
  obtain ⟨c1, l1, hf1⟩ := hf1
  obtain ⟨c2, l2, hf2⟩ := hf2
  obtain ⟨c3, l3, hf3⟩ := hf3
  let fA1 : U →ᵃ[F] F := l1.toAffineMap + AffineMap.const F U c1
  let fA2 : U →ᵃ[F] F := l2.toAffineMap + AffineMap.const F U c2
  let fA3 : U →ᵃ[F] F := l3.toAffineMap + AffineMap.const F U c3
  have hfA1 (x : U) : fA1 x = f1 x := by change l1 x + c1 = f1 x; rw [hf1]; ring
  have hfA2 (x : U) : fA2 x = f2 x := by change l2 x + c2 = f2 x; rw [hf2]; ring
  have hfA3 (x : U) : fA3 x = f3 x := by change l3 x + c3 = f3 x; rw [hf3]; ring
  have hcore (t : T) (l : (J → F) →ᵃ[F] F) :
      |∑ z, sign8 ((∑ i, A i (sel.linear v0) * u i (e.symm (t, z)) *
        v i (e.symm (t, z))) + l z)| ≤ ((2 ^ (Fintype.card J - d) : ℕ) : ℤ) := by
    simp_rw [hselshift, hu, hv]
    have hp := hpair I J pos (fun i => A i s) a.2 l
    have hexp : Fintype.card J - (Finset.univ.filter fun i => A i s ≠ 0).card ≤
        Fintype.card J - d := by
      exact Nat.sub_le_sub_left (show d ≤ (Finset.univ.filter fun i => A i s ≠ 0).card by simpa [helper3_codeWeight] using hweight) _
    exact hp.trans (by exact_mod_cast Nat.pow_le_pow_right (by omega : 0 < 2) hexp)
  have hb := h8_selector_q2_product_fiber_natAbs_bound e sel (fun t : T => a.1 + (t : S))
    hsel A h u v q0 hq0 fA1 fA2 fA3 v0 (2 ^ (Fintype.card J - d)) hcore
  have heq (x : U) :
      sign8 ((h (sel x) + ∑ i, A i (sel x) * u i x * v i x) +
        q0 x + fA1 x * fA2 x * fA3 x) = phaseSign (codePhase pos A h a L q x) := by
    rw [hfA1, hfA2, hfA3]
    unfold sign8 phaseSign
    congr 1
    unfold codePhase
    rw [hq]
    have hsx : sel x = (a + L x).1 := by change (L x).1 + a.1 = a.1 + (L x).1; exact add_comm _ _
    have hux (i : I) : u i x = (a + L x).2 (pos (i, false)) := by
      change (L x).2 (pos (i, false)) + a.2 (pos (i, false)) = a.2 (pos (i, false)) + (L x).2 (pos (i, false))
      ring
    have hvx (i : I) : v i x = (a + L x).2 (pos (i, true)) := by
      change (L x).2 (pos (i, true)) + a.2 (pos (i, true)) = a.2 (pos (i, true)) + (L x).2 (pos (i, true))
      ring
    simp_rw [hsx, hux, hvx]
    ring
  simp_rw [heq] at hb
  have hcard := terminal_coordinate_card e
  rw [hcard] at hb ⊢
  exact pair_sum_to_normalized_line d (Fintype.card J) (Fintype.card T) _ hd hdj hb

namespace PairTransport

abbrev F := ZMod 2

def chi (a : F) : ℤ := if a = 0 then 1 else -1

lemma f2_cases (a : F) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma chi_add (a b : F) : chi (a + b) = chi a * chi b := by
  rcases f2_cases a with rfl | rfl <;> rcases f2_cases b with rfl | rfl <;> rfl

lemma chi_natAbs (a : F) : (chi a).natAbs = 1 := by
  rcases f2_cases a with rfl | rfl <;> rfl

abbrev Rest {I J : Type*} (pos : I × Bool ↪ J) := {j : J // ∀ p : I × Bool, pos p ≠ j}

noncomputable def indexEquiv {I J : Type*} (pos : I × Bool ↪ J) :
    (I × Bool) ⊕ Rest pos ≃ J :=
  Equiv.ofBijective (Sum.elim pos (fun r => r.val)) (by
    constructor
    · rintro (p | p) (q | q) heq
      · exact congrArg Sum.inl (pos.injective heq)
      · exact False.elim (q.property p heq)
      · exact False.elim (p.property q heq.symm)
      · exact congrArg Sum.inr (Subtype.ext heq)
    · intro j
      classical
      by_cases hj : ∃ p : I × Bool, pos p = j
      · obtain ⟨p, hp⟩ := hj
        exact ⟨Sum.inl p, hp⟩
      · exact ⟨Sum.inr ⟨j, by simpa using hj⟩, rfl⟩)

noncomputable def pack {I J : Type*} (pos : I × Bool ↪ J)
    (u v : I → F) (z : Rest pos → F) : J → F :=
  fun j => Sum.elim (fun p => if p.2 then v p.1 else u p.1) z ((indexEquiv pos).symm j)

lemma pack_pair {I J : Type*} (pos : I × Bool ↪ J)
    (u v : I → F) (z : Rest pos → F) (i : I) (b : Bool) :
    pack pos u v z (pos (i, b)) = if b then v i else u i := by
  change Sum.elim _ z ((indexEquiv pos).symm ((indexEquiv pos) (Sum.inl (i, b)))) = _
  rw [Equiv.symm_apply_apply]
  rfl

lemma pack_rest {I J : Type*} (pos : I × Bool ↪ J)
    (u v : I → F) (z : Rest pos → F) (j : Rest pos) :
    pack pos u v z j.val = z j := by
  change Sum.elim _ z ((indexEquiv pos).symm ((indexEquiv pos) (Sum.inr j))) = _
  rw [Equiv.symm_apply_apply]
  rfl

noncomputable def assignmentEquiv {I J : Type*} (pos : I × Bool ↪ J) :
    (I → F) × ((I → F) × (Rest pos → F)) ≃ (J → F) where
  toFun p := pack pos p.1 p.2.1 p.2.2
  invFun x := (fun i => x (pos (i, false)), (fun i => x (pos (i, true)), fun j => x j.val))
  left_inv p := by
    apply Prod.ext
    · funext i
      exact pack_pair pos p.1 p.2.1 p.2.2 i false
    · apply Prod.ext
      · funext i
        exact pack_pair pos p.1 p.2.1 p.2.2 i true
      · funext j
        exact pack_rest pos p.1 p.2.1 p.2.2 j
  right_inv x := by
    funext j
    classical
    by_cases hj : ∃ p : I × Bool, pos p = j
    · obtain ⟨⟨i, b⟩, rfl⟩ := hj
      change pack pos (fun i => x (pos (i, false)))
        (fun i => x (pos (i, true))) (fun j => x j.val) (pos (i, b)) = _
      rw [pack_pair]
      cases b <;> rfl
    · exact pack_rest pos _ _ _ ⟨j, by simpa using hj⟩

lemma card_coordinates {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (pos : I × Bool ↪ J) :
    Fintype.card J = 2 * Fintype.card I + Fintype.card (Rest pos) := by
  have h := Fintype.card_congr (indexEquiv pos)
  simpa [Fintype.card_sum, Fintype.card_prod, Nat.mul_comm] using h.symm

lemma affine_coefficients {J : Type*} [Fintype J] (a : (J → F) →ᵃ[F] F) :
    ∃ l : J → F, ∀ x : J → F, a x = a 0 + ∑ j, l j * x j := by
  classical
  refine ⟨fun j => a.linear (Pi.single j 1), fun x => ?_⟩
  have hx : x = ∑ j : J, x j • Pi.single j (1 : F) := by
    ext j
    simp [Pi.single_apply, mul_ite]
  have ha : a x = a.linear x + a 0 := by simpa using a.map_vadd 0 x
  have hlin : a.linear x = ∑ j : J, a.linear (Pi.single j 1) * x j := by
    calc
      _ = a.linear (∑ j : J, x j • Pi.single j (1 : F)) := congrArg a.linear hx
      _ = _ := by
        rw [map_sum]
        simp only [map_smul, smul_eq_mul]
        apply Finset.sum_congr rfl
        intro j _
        ring
  rw [ha, hlin, add_comm]

lemma affine_sum_pack {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (pos : I × Bool ↪ J) (l : J → F) (u v : I → F) (z : Rest pos → F) :
    (∑ j : J, l j * pack pos u v z j) =
      (∑ i : I, (l (pos (i, false)) * u i + l (pos (i, true)) * v i)) +
        ∑ j : Rest pos, l j.val * z j := by
  calc
    _ = ∑ p : (I × Bool) ⊕ Rest pos,
        l (indexEquiv pos p) * pack pos u v z (indexEquiv pos p) :=
      ((indexEquiv pos).sum_comp _).symm
    _ = _ := by
      rw [Fintype.sum_sum_type]
      change (∑ p : I × Bool, l (pos p) * pack pos u v z (pos p)) +
        (∑ j : Rest pos, l j.val * pack pos u v z j.val) = _
      simp_rw [Fintype.sum_prod_type, pack_pair, pack_rest]
      simp [add_comm]

lemma natAbs_sum_le_card {T : Type*} [Fintype T] (f : T → F) :
    (∑ t : T, chi (f t)).natAbs ≤ Fintype.card T := by
  classical
  have h : ∀ s : Finset T, (∑ t ∈ s, chi (f t)).natAbs ≤ s.card := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert t s ht ih =>
      rw [Finset.sum_insert ht, Finset.card_insert_of_notMem ht]
      calc
        _ ≤ (chi (f t)).natAbs + (∑ a ∈ s, chi (f a)).natAbs := Int.natAbs_add_le _ _
        _ ≤ 1 + s.card := Nat.add_le_add (le_of_eq (chi_natAbs _)) ih
        _ = _ := Nat.add_comm _ _
  simpa using h Finset.univ

lemma chi_sum {I : Type*} (s : Finset I) (f : I → F) :
    chi (∑ i ∈ s, f i) = ∏ i ∈ s, chi (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, chi_add, ih]

lemma sum_uv_factor {I : Type*} [Fintype I] [DecidableEq I] (c a b : I → F) :
    (∑ u : I → F, ∑ v : I → F,
      chi (∑ i : I, (c i * u i * v i + a i * u i + b i * v i))) =
    ∏ i : I, ∑ p : F × F, chi (c i * p.1 * p.2 + a i * p.1 + b i * p.2) := by
  let G : I → F × F → ℤ := fun i p => chi (c i * p.1 * p.2 + a i * p.1 + b i * p.2)
  have hps : (∏ i : I, ∑ p : F × F, G i p) =
      ∑ f : I → F × F, ∏ i : I, G i (f i) := Fintype.prod_sum G
  rw [hps]
  let ePair : ((I → F) × (I → F)) ≃ (I → F × F) :=
    { toFun := fun p i => (p.1 i, p.2 i)
      invFun := fun f => (fun i => (f i).1, fun i => (f i).2)
      left_inv := fun ⟨_, _⟩ => rfl
      right_inv := fun _ => rfl }
  rw [← Fintype.sum_prod_type', ← ePair.sum_comp]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [chi_sum]
  rfl

lemma two_bit_bound (c a b : F) :
    (∑ p : F × F, chi (c * p.1 * p.2 + a * p.1 + b * p.2)).natAbs ≤
      if c ≠ 0 then 2 else 4 := by
  rcases f2_cases c with rfl | rfl <;> rcases f2_cases a with rfl | rfl <;>
    rcases f2_cases b with rfl | rfl <;> decide

lemma prod_two_four {I : Type*} (s : Finset I) (P : I → Prop) [DecidablePred P] :
    (∏ i ∈ s, if P i then (2 : ℕ) else 4) =
      2 ^ (2 * s.card - (s.filter P).card) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have hle : (s.filter P).card ≤ s.card := Finset.card_filter_le _ _
    have hnot : i ∉ s.filter P := fun h => hi (Finset.mem_filter.mp h).1
    by_cases hp : P i
    · rw [Finset.prod_insert hi, ite_eq_left hp, Finset.card_insert_of_notMem hi,
        Finset.filter_insert, ite_eq_left hp, Finset.card_insert_of_notMem hnot, ih]
      rw [show 2 * (s.card + 1) - ((s.filter P).card + 1) =
        (2 * s.card - (s.filter P).card) + 1 by omega, pow_succ]
      ring
    · rw [Finset.prod_insert hi, ite_eq_right hp, Finset.card_insert_of_notMem hi,
        Finset.filter_insert, ite_eq_right hp, ih]
      rw [show 2 * (s.card + 1) - (s.filter P).card =
        (2 * s.card - (s.filter P).card) + 2 by omega, pow_add]
      ring

lemma canonical_pair_bound {I : Type*} [Fintype I] [DecidableEq I] (c a b : I → F) :
    (∑ u : I → F, ∑ v : I → F,
      chi (∑ i : I, (c i * u i * v i + a i * u i + b i * v i))).natAbs ≤
      2 ^ (2 * Fintype.card I -
        ((Finset.univ : Finset I).filter (fun i => c i ≠ 0)).card) := by
  classical
  rw [sum_uv_factor, Int.natAbs_prod]
  calc
    _ ≤ ∏ i : I, if c i ≠ 0 then (2 : ℕ) else 4 :=
      Finset.prod_le_prod (fun i _ => two_bit_bound _ _ _)
    _ = _ := by simpa using prod_two_four (Finset.univ : Finset I) (fun i => c i ≠ 0)

lemma affine_pair_factorization {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (pos : I × Bool ↪ J) (c : I → F) (a : (J → F) →ᵃ[F] F) :
    ∃ l : J → F,
      (∑ x : J → F, chi (a x + ∑ i : I,
        c i * x (pos (i, false)) * x (pos (i, true)))) =
      chi (a 0) * (∑ u : I → F, ∑ v : I → F,
        chi (∑ i : I, (c i * u i * v i + l (pos (i, false)) * u i +
          l (pos (i, true)) * v i))) *
        (∑ z : Rest pos → F, chi (∑ j : Rest pos, l j.val * z j)) := by
  classical
  obtain ⟨l, hl⟩ := affine_coefficients a
  refine ⟨l, ?_⟩
  have hphase (u v : I → F) (z : Rest pos → F) :
      a (pack pos u v z) + ∑ i : I,
        c i * pack pos u v z (pos (i, false)) * pack pos u v z (pos (i, true)) =
      a 0 + (∑ i : I, (c i * u i * v i + l (pos (i, false)) * u i +
        l (pos (i, true)) * v i)) + ∑ j : Rest pos, l j.val * z j := by
    rw [hl, affine_sum_pack]
    simp_rw [pack_pair]
    simp only [Bool.false_eq_true, ite_false, ite_true, Finset.sum_add_distrib]
    ring
  calc
    _ = ∑ p : (I → F) × ((I → F) × (Rest pos → F)),
        chi (a (pack pos p.1 p.2.1 p.2.2) + ∑ i : I,
          c i * pack pos p.1 p.2.1 p.2.2 (pos (i, false)) *
            pack pos p.1 p.2.1 p.2.2 (pos (i, true))) :=
      ((assignmentEquiv pos).sum_comp _).symm
    _ = _ := by
      simp only [Fintype.sum_prod_type]
      simp_rw [hphase, chi_add]
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
      simp_rw [← Finset.mul_sum]

lemma retained_pair_bound {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (pos : I × Bool ↪ J) (c : I → F) (a : (J → F) →ᵃ[F] F) :
    (∑ x : J → F, chi (a x + ∑ i : I,
      c i * x (pos (i, false)) * x (pos (i, true)))).natAbs ≤
      2 ^ (Fintype.card J -
        ((Finset.univ : Finset I).filter (fun i => c i ≠ 0)).card) := by
  classical
  obtain ⟨l, hl⟩ := affine_pair_factorization pos c a
  rw [hl, Int.natAbs_mul, Int.natAbs_mul, chi_natAbs, one_mul]
  have hpair := canonical_pair_bound c (fun i => l (pos (i, false)))
    (fun i => l (pos (i, true)))
  have hrest := natAbs_sum_le_card (fun z : Rest pos → F => ∑ j : Rest pos, l j.val * z j)
  have hcard : Fintype.card (Rest pos → F) = 2 ^ Fintype.card (Rest pos) := by simp [ZMod.card]
  rw [hcard] at hrest
  have hactive : ((Finset.univ : Finset I).filter (fun i => c i ≠ 0)).card ≤
      Fintype.card I := (Finset.card_filter_le _ _).trans_eq (by simp)
  have hcoords := card_coordinates pos
  calc
    _ ≤ 2 ^ (2 * Fintype.card I -
        ((Finset.univ : Finset I).filter (fun i => c i ≠ 0)).card) *
        2 ^ Fintype.card (Rest pos) := Nat.mul_le_mul hpair hrest
    _ = _ := by
      rw [← pow_add]
      congr 1
      omega

lemma retained_active_pair_bound {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (pos : I × Bool ↪ J) (a : (J → F) →ᵃ[F] F) :
    (∑ x : J → F, chi (a x + ∑ i : I,
      x (pos (i, false)) * x (pos (i, true)))).natAbs ≤
      2 ^ (Fintype.card J - Fintype.card I) := by
  simpa using retained_pair_bound pos (fun _ => (1 : F)) a

end PairTransport

namespace SelectorHCore

open PairTransport

def coord {J : Type*} (j : J) : (J → F) →ᵃ[F] F :=
  (LinearMap.proj j).toAffineMap

noncomputable def offsetCorrection {I J : Type*} [Fintype I]
    (pos : I × Bool ↪ J) (c u v : I → F) : (J → F) →ᵃ[F] F :=
  ∑ i : I, ((c i * u i) • coord (pos (i, true)) +
    (c i * v i) • coord (pos (i, false)) +
    AffineMap.const F (J → F) (c i * u i * v i))

lemma offsetCorrection_apply {I J : Type*} [Fintype I]
    (pos : I × Bool ↪ J) (c u v : I → F) (x : J → F) :
    offsetCorrection pos c u v x =
      ∑ i : I, (c i * u i * x (pos (i, true)) +
        c i * v i * x (pos (i, false)) + c i * u i * v i) := by
  simp [offsetCorrection, coord, smul_eq_mul]

lemma offset_phase {I J : Type*} [Fintype I]
    (pos : I × Bool ↪ J) (c u v : I → F) (l : (J → F) →ᵃ[F] F) (x : J → F) :
    (∑ i : I, c i * (x (pos (i, false)) + u i) * (x (pos (i, true)) + v i)) + l x =
      (l + offsetCorrection pos c u v) x +
        ∑ i : I, c i * x (pos (i, false)) * x (pos (i, true)) := by
  change (∑ i : I, c i * (x (pos (i, false)) + u i) * (x (pos (i, true)) + v i)) + l x =
    (l x + offsetCorrection pos c u v x) +
      ∑ i : I, c i * x (pos (i, false)) * x (pos (i, true))
  rw [offsetCorrection_apply]
  simp only [Finset.sum_add_distrib]
  calc
    _ = (∑ i : I, (c i * x (pos (i, false)) * x (pos (i, true)) +
        c i * u i * x (pos (i, true)) + c i * v i * x (pos (i, false)) +
        c i * u i * v i)) + l x := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by simp only [Finset.sum_add_distrib]; ring

lemma affine_offset_pair_bound {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (pos : I × Bool ↪ J) (c u v : I → F) (l : (J → F) →ᵃ[F] F) :
    (∑ x : J → F,
      chi ((∑ i : I, c i * (x (pos (i, false)) + u i) *
        (x (pos (i, true)) + v i)) + l x)).natAbs ≤
      2 ^ (Fintype.card J -
        ((Finset.univ : Finset I).filter (fun i => c i ≠ 0)).card) := by
  simp_rw [offset_phase]
  exact retained_pair_bound pos c (l + offsetCorrection pos c u v)

lemma affine_offset_pair_bound_int {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (pos : I × Bool ↪ J) (c u v : I → F) (l : (J → F) →ᵃ[F] F) :
    |∑ x : J → F,
      chi ((∑ i : I, c i * (x (pos (i, false)) + u i) *
        (x (pos (i, true)) + v i)) + l x)| ≤
      ((2 ^ (Fintype.card J -
        ((Finset.univ : Finset I).filter (fun i => c i ≠ 0)).card) : ℕ) : ℤ) := by
  have h := affine_offset_pair_bound pos c u v l
  rw [← Int.natCast_natAbs]
  exact_mod_cast h

end SelectorHCore

lemma terminal_line_oracle (S : Type) [AddCommGroup S] [Module F S]
    (d : ℕ) (hd : 0 < d) :
    TerminalLineOracle S d (2 ^ d) (2 ^ (d - 1) + 1) := by
  apply terminal_line_of_embedded_walsh _ S d hd
  intro I J _ _ _ _ pos w p l
  have hh := SelectorHCore.affine_offset_pair_bound_int pos w
    (fun i => p (pos (i, false))) (fun i => p (pos (i, true))) l
  simpa only [PairTransport.chi, sign8, add_comm, Nat.cast_pow, Nat.cast_ofNat] using hh

end PEqualNP.Outside.L_meta_32057_aux

namespace PEqualNP.Outside.L_meta_32057_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open scoped BigOperators
open Classical

lemma extend_form_free {k : ℕ} (gs : List Gate) (g : Gate)
    (hleg : legalGates k (gs ++ [g]))
    (hfree : ¬ ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2))
    (P : (Fin k → F2) → F2)
    (hih : ∀ w < k + gs.length, ∃ (lin : Fin k → F2) (c e : F2),
      ∀ y : Fin k → F2, (wiresOf gs (bitsOf k y)).getD w false =
        decide (dotProduct lin y + c + e * P y = 1)) :
    ∀ w < k + (gs ++ [g]).length, ∃ (lin : Fin k → F2) (c e : F2),
      ∀ y : Fin k → F2, (wiresOf (gs ++ [g]) (bitsOf k y)).getD w false =
        decide (dotProduct lin y + c + e * P y = 1) := by
  intro w hw
  have hpre := legalGates_prefix hleg
  simp only [List.length_append, List.length_singleton] at hw
  by_cases hlt : w < k + gs.length
  · obtain ⟨lin, c, e, hlin⟩ := hih w hlt
    refine ⟨lin, c, e, fun y => ?_⟩
    rw [wiresOf_append_getD_lt gs [g] (bitsOf k y) (by rw [bitsOf_len]; exact hlt)]
    exact hlin y
  · have hweq : w = k + gs.length := by omega
    subst hweq
    have hback := hpre.2.1
    have hshape := hpre.2.2
    have eval_snoc : ∀ y : Fin k → F2,
        (wiresOf (gs ++ [g]) (bitsOf k y)).getD (k + gs.length) false =
          g.op.eval (g.inputs.map fun i => (wiresOf gs (bitsOf k y)).getD i false) :=
      fun y => wiresOf_snoc_last_eq gs g (bitsOf k y) (bitsOf_len k y)
    rcases hshape.2 with hop | hop | hop | ⟨hop, hlen1⟩
    · rcases hg : g.inputs with _ | ⟨w0, rest⟩
      · refine ⟨0, 1, 0, fun y => ?_⟩
        rw [eval_snoc y, hop, hg]; simp [GateOp.eval]
      · rcases rest with _ | ⟨w1, rest2⟩
        · obtain ⟨lin, c, e, hlin⟩ := hih w0 (hback w0 (by rw [hg]; simp))
          refine ⟨lin, c, e, fun y => ?_⟩
          rw [eval_snoc y, hop, hg]
          simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
          exact hlin y
        · rcases rest2 with _ | ⟨_, _⟩
          · exfalso; exact hfree ⟨Or.inl hop, by rw [hg]; rfl⟩
          · exfalso; have := hshape.1; rw [hg] at this; simp at this
    · rcases hg : g.inputs with _ | ⟨w0, rest⟩
      · refine ⟨0, 0, 0, fun y => ?_⟩
        rw [eval_snoc y, hop, hg]; simp [GateOp.eval]
      · rcases rest with _ | ⟨w1, rest2⟩
        · obtain ⟨lin, c, e, hlin⟩ := hih w0 (hback w0 (by rw [hg]; simp))
          refine ⟨lin, c, e, fun y => ?_⟩
          rw [eval_snoc y, hop, hg]
          simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
          exact hlin y
        · rcases rest2 with _ | ⟨_, _⟩
          · exfalso; exact hfree ⟨Or.inr hop, by rw [hg]; rfl⟩
          · exfalso; have := hshape.1; rw [hg] at this; simp at this
    · rcases hg : g.inputs with _ | ⟨w0, rest⟩
      · refine ⟨0, 1, 0, fun y => ?_⟩
        rw [eval_snoc y, hop, hg]; simp [GateOp.eval]
      · rcases rest with _ | ⟨w1, rest2⟩
        · obtain ⟨lin, c, e, hlin⟩ := hih w0 (hback w0 (by rw [hg]; simp))
          refine ⟨lin, c + 1, e, fun y => ?_⟩
          rw [eval_snoc y, hop, hg]
          simp only [List.map_cons, List.map_nil, hlin y, GateOp.eval]
          have heq : dotProduct lin y + (c + 1) + e * P y =
              (dotProduct lin y + c + e * P y) + 1 := by ring
          rw [heq]
          rcases zmod2_cases (dotProduct lin y + c + e * P y) with h | h <;> rw [h] <;> decide
        · rcases rest2 with _ | ⟨_, _⟩
          · obtain ⟨lin0, c0, e0, hlin0⟩ := hih w0 (hback w0 (by rw [hg]; simp))
            obtain ⟨lin1, c1, e1, hlin1⟩ := hih w1 (hback w1 (by rw [hg]; simp))
            refine ⟨lin0 + lin1, c0 + c1 + 1, e0 + e1, fun y => ?_⟩
            rw [eval_snoc y, hop, hg]
            simp only [List.map_cons, List.map_nil, hlin0 y, hlin1 y, GateOp.eval, add_dotProduct]
            have hrw : dotProduct lin0 y + dotProduct lin1 y + (c0 + c1 + 1) +
                (e0 + e1) * P y =
                (dotProduct lin0 y + c0 + e0 * P y) +
                (dotProduct lin1 y + c1 + e1 * P y) + 1 := by ring
            rw [hrw]
            rcases zmod2_cases (dotProduct lin0 y + c0 + e0 * P y) with h0 | h0 <;>
              rcases zmod2_cases (dotProduct lin1 y + c1 + e1 * P y) with h1 | h1 <;>
              rw [h0, h1] <;> decide
          · exfalso; have := hshape.1; rw [hg] at this; simp at this
    · rcases hg : g.inputs with _ | ⟨w0, rest⟩
      · simp [hg] at hlen1
      · rcases rest with _ | ⟨_, _⟩
        · obtain ⟨lin, c, e, hlin⟩ := hih w0 (hback w0 (by rw [hg]; simp))
          refine ⟨lin, c + 1, e, fun y => ?_⟩
          rw [eval_snoc y, hop, hg]
          simp only [List.map_cons, List.map_nil, hlin y, GateOp.eval, List.headD_cons]
          have heq : dotProduct lin y + (c + 1) + e * P y =
              (dotProduct lin y + c + e * P y) + 1 := by ring
          rw [heq]
          rcases zmod2_cases (dotProduct lin y + c + e * P y) with h | h <;> rw [h] <;> decide
        · simp [hg] at hlen1

lemma zmod2_or_decide (a b : F2) :
    (decide (a = 1) || decide (b = 1)) = decide (a + b + a * b = 1) := by
  fin_cases a <;> fin_cases b <;> decide

lemma cost_one_common_product {k : ℕ} (gs : List Gate)
    (hleg : legalGates k gs) (hcost : costGates gs ≤ 1) :
    ∃ (u v : Fin k → F2) (a b : F2),
      ∀ w < k + gs.length, ∃ (lin : Fin k → F2) (c e : F2),
        ∀ y : Fin k → F2, (wiresOf gs (bitsOf k y)).getD w false =
          decide (dotProduct lin y + c + e *
            ((dotProduct u y + a) * (dotProduct v y + b)) = 1) := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨0, 0, 0, 0, ?_⟩
    intro w hw
    simp only [List.length_nil, Nat.add_zero] at hw
    refine ⟨Pi.single ⟨w, hw⟩ 1, 0, 0, fun y => ?_⟩
    change (bitsOf k y).getD (⟨w, hw⟩ : Fin k).val false = _
    rw [bitsOf_getD, single_dotProduct]
    simp
  | append_singleton gs g ih =>
    have hpre := legalGates_prefix hleg
    by_cases hpaid : (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2
    · have hcost_app := costGates_snoc_one gs g hpaid
      have hzero : costGates gs = 0 := by omega
      have hAffine := cost_zero_affine gs hpre.1 hzero
      obtain ⟨w0, w1, hins⟩ : ∃ w0 w1, g.inputs = [w0, w1] := by
        rcases hx : g.inputs with _ | ⟨w0, _ | ⟨w1, rest⟩⟩
        · simp [hx] at hpaid
        · simp [hx] at hpaid
        · have hr : rest = [] := by simpa [hx] using hpaid.2
          exact ⟨w0, w1, by rw [hr]⟩
      obtain ⟨u, a, hu⟩ := hAffine w0 (hpre.2.1 w0 (by rw [hins]; simp))
      obtain ⟨v, b, hv⟩ := hAffine w1 (hpre.2.1 w1 (by rw [hins]; simp))
      refine ⟨u, v, a, b, ?_⟩
      intro w hw
      simp only [List.length_append, List.length_singleton] at hw
      by_cases hlt : w < k + gs.length
      · obtain ⟨l, c, hl⟩ := hAffine w hlt
        refine ⟨l, c, 0, fun y => ?_⟩
        rw [wiresOf_append_getD_lt gs [g] (bitsOf k y) (by rw [bitsOf_len]; exact hlt)]
        simpa using hl y
      · have heq : w = k + gs.length := by omega
        subst heq
        have eval_snoc := fun y => wiresOf_snoc_last_eq gs g (bitsOf k y) (bitsOf_len k y)
        rcases hpaid.1 with hop | hop
        · refine ⟨0, 0, 1, fun y => ?_⟩
          rw [eval_snoc y, hop, hins]
          simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
            id_eq, Bool.and_true, hu y, hv y, zero_dotProduct, zero_add, one_mul]
          exact (zmod2_mul_decide _ _).symm
        · refine ⟨u + v, a + b, 1, fun y => ?_⟩
          rw [eval_snoc y, hop, hins]
          simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
            id_eq, Bool.or_false, hu y, hv y, add_dotProduct, one_mul]
          rw [zmod2_or_decide]
          congr 1
          ring
    · have hcost_app := costGates_snoc_zero gs g hpaid
      obtain ⟨u, v, a, b, hforms⟩ := ih hpre.1 (by omega)
      exact ⟨u, v, a, b, extend_form_free gs g hleg hpaid
        (fun y => (dotProduct u y + a) * (dotProduct v y + b)) hforms⟩

lemma common_product_phase {k : ℕ}
    (u v : (Fin k → F2) → F2) (lin : Fin k → Fin k → F2)
    (cn coeff l : Fin k → F2) (c δ : F2) :
    ∃ q : (Fin k → F2) → F2, isQuad q ∧ ∀ y,
      (dotProduct l y + c + δ * (u y * v y)) +
        dotProduct (fun j => dotProduct (lin j) y + cn j + coeff j * (u y * v y)) y =
      q y + u y * v y * (dotProduct coeff y + δ) := by
  let q := fun y : Fin k → F2 => c + dotProduct (l + cn) y +
    ∑ i, ∑ j, lin i j * y i * y j
  refine ⟨q, ⟨c, l + cn, lin, fun _ => rfl⟩, ?_⟩
  intro y
  have hlin : ∑ i, dotProduct (lin i) y * y i =
      ∑ i, ∑ j, lin i j * y i * y j := by
    unfold dotProduct
    simp_rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hnonlin : ∑ i, coeff i * (u y * v y) * y i =
      u y * v y * dotProduct coeff y := by
    unfold dotProduct
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  change _ = c + dotProduct (l + cn) y +
    (∑ i, ∑ j, lin i j * y i * y j) + u y * v y * (dotProduct coeff y + δ)
  rw [add_dotProduct]
  have hdot : dotProduct (fun j => dotProduct (lin j) y + cn j + coeff j * (u y * v y)) y =
      (∑ i, ∑ j, lin i j * y i * y j) + dotProduct cn y +
        u y * v y * dotProduct coeff y := by
    change (∑ i, (dotProduct (lin i) y + cn i + coeff i * (u y * v y)) * y i) = _
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hlin, hnonlin]
    rfl
  rw [hdot]
  ring

lemma cost_one_phase {k : ℕ} (C : Circuit)
    (hleg : legalGates k C.gates) (hcost : costGates C.gates ≤ 1)
    (houtput : C.output < k + C.gates.length)
    (tap : Fin k → ℕ) (htap : ∀ j, tap j < k + C.gates.length) :
    ∃ (u v t : Fin k → F2) (a b c : F2) (q : (Fin k → F2) → F2),
      isQuad q ∧ ∀ y,
        (if C.eval (bitsOf k y) then (1 : F2) else 0) +
          dotProduct (fun j => if (C.wires (bitsOf k y)).getD (tap j) false
            then (1 : F2) else 0) y =
        q y + (dotProduct u y + a) * (dotProduct v y + b) * (dotProduct t y + c) := by
  classical
  obtain ⟨u, v, a, b, hforms⟩ := cost_one_common_product C.gates hleg hcost
  obtain ⟨l, c, δ, hout⟩ := hforms C.output houtput
  choose lin cn coeff hparts using fun j => hforms (tap j) (htap j)
  obtain ⟨q, hq, hphase⟩ := common_product_phase
    (fun y => dotProduct u y + a) (fun y => dotProduct v y + b) lin cn coeff l c δ
  refine ⟨u, v, coeff, a, b, δ, q, hq, ?_⟩
  intro y
  have ho : (if C.eval (bitsOf k y) then (1 : F2) else 0) =
      dotProduct l y + c + δ * ((dotProduct u y + a) * (dotProduct v y + b)) := by
    change (if (wiresOf C.gates (bitsOf k y)).getD C.output false then (1 : F2) else 0) = _
    rw [hout y, zmod2_decide_bool]
  have hp : (fun j => if (C.wires (bitsOf k y)).getD (tap j) false then (1 : F2) else 0) =
      fun j => dotProduct (lin j) y + cn j + coeff j *
        ((dotProduct u y + a) * (dotProduct v y + b)) := by
    funext j
    change (if (wiresOf C.gates (bitsOf k y)).getD (tap j) false then (1 : F2) else 0) = _
    rw [hparts j y, zmod2_decide_bool]
  rw [ho, hp]
  exact hphase y




lemma row_rank_tiers (b r t denom plane line : ℕ)
    (hr : r ≤ b) (ht : t ≤ 2 ^ r)
    (hsmall : denom ≤ 4 * max plane line)
    (hfull : r = b → denom * t ≤ 2 ^ b * plane)
    (hone : r + 1 = b → denom * t ≤ 2 ^ b * line) :
    denom * t ≤ 2 ^ b * max plane line := by
  by_cases htop : r = b
  · exact (hfull htop).trans (Nat.mul_le_mul_left _ (le_max_left _ _))
  by_cases hnext : r + 1 = b
  · exact (hone hnext).trans (Nat.mul_le_mul_left _ (le_max_right _ _))
  have hlow : r + 2 ≤ b := by omega
  calc
    denom * t ≤ denom * 2 ^ r := Nat.mul_le_mul_left _ ht
    _ ≤ (4 * max plane line) * 2 ^ r := Nat.mul_le_mul_right _ hsmall
    _ = 2 ^ (r + 2) * max plane line := by rw [Nat.pow_add]; ring
    _ ≤ 2 ^ b * max plane line :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) hlow)

lemma row_weighted_bound {ι : Type*} [Fintype ι]
    (w t : ι → ℕ) (n b denom mass raw : ℕ)
    (hweight : ∑ i, w i = 2 ^ n)
    (hraw : raw ≤ ∑ i, w i * t i)
    (hrow : ∀ i, denom * t i ≤ 2 ^ b * mass) :
    denom * raw ≤ 2 ^ (n + b) * mass := by
  calc
    denom * raw ≤ denom * ∑ i, w i * t i := Nat.mul_le_mul_left _ hraw
    _ = ∑ i, w i * (denom * t i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ ∑ i, w i * (2 ^ b * mass) := by
      exact Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left _ (hrow i))
    _ = (∑ i, w i) * (2 ^ b * mass) := (Finset.sum_mul _ _ _).symm
    _ = 2 ^ n * (2 ^ b * mass) := by rw [hweight]
    _ = 2 ^ (n + b) * mass := by rw [Nat.pow_add]; ring

lemma row_decomposition_tiers {ι : Type*} [Fintype ι]
    (r t : ι → ℕ) (n b denom plane line raw : ℕ)
    (hweight : ∑ i, 2 ^ (n - r i) = 2 ^ n)
    (hraw : raw ≤ ∑ i, 2 ^ (n - r i) * t i)
    (hr : ∀ i, r i ≤ b) (ht : ∀ i, t i ≤ 2 ^ r i)
    (hsmall : denom ≤ 4 * max plane line)
    (hfull : ∀ i, r i = b → denom * t i ≤ 2 ^ b * plane)
    (hone : ∀ i, r i + 1 = b → denom * t i ≤ 2 ^ b * line) :
    denom * raw ≤ 2 ^ (n + b) * max plane line := by
  apply row_weighted_bound (fun i => 2 ^ (n - r i)) t n b denom
    (max plane line) raw hweight hraw
  intro i
  exact row_rank_tiers b (r i) (t i) denom plane line
    (hr i) (ht i) hsmall (hfull i) (hone i)


noncomputable def rowResidual (n : ℕ) (g : (Fin n → F2) → F2)
    (W : Submodule F2 (Fin n → F2)) (a : Fin n → F2)
    (D : Circuit) (tap : Fin n → ℕ) : ℕ :=
  (∑ y : Fin n → F2, if y - a ∈ W then
    signBool (Bool.xor (D.eval (bitsOf n y))
      (decide (dotProduct (fun j : Fin n =>
        if (D.wires (bitsOf n y)).getD (tap j) false then (1 : F2) else 0) y = 1))) *
      signBool (decide (g y = 1))
    else 0).natAbs

lemma row_raw_bound_of_tiers (n b denom plane line : ℕ)
    (g : (Fin n → F2) → F2)
    (hsmall : denom ≤ 4 * max plane line)
    (hfull : ∀ (W : Submodule F2 (Fin n → F2)) (a : Fin n → F2)
        (D : Circuit) (tap : Fin n → ℕ),
      Module.finrank F2 W = b → legalGates n D.gates → costGates D.gates = 0 →
      D.output < n + D.size → (∀ j, tap j < n + D.size) →
      denom * rowResidual n g W a D tap ≤ 2 ^ b * plane)
    (hone : ∀ (W : Submodule F2 (Fin n → F2)) (a : Fin n → F2)
        (D : Circuit) (tap : Fin n → ℕ),
      Module.finrank F2 W + 1 = b → legalGates n D.gates → costGates D.gates ≤ 1 →
      D.output < n + D.size → (∀ j, tap j < n + D.size) →
      denom * rowResidual n g W a D tap ≤ 2 ^ b * line)
    (C : Circuit) (hleg : legalGates (2 * n) C.gates) (hcost : costGates C.gates ≤ b) :
    denom * (∑ x : Fin n → F2, ∑ y : Fin n → F2,
      if C.eval (bitsOf n x ++ bitsOf n y) = decide (dotProduct x y + g y = 1)
      then (1 : ℤ) else -1).natAbs ≤ 2 ^ (n + b) * max plane line := by
  rcases forward_decomp_bounds n b g C hleg hcost with
    ⟨N, r, W, a, D, tap, _, hmeta, hsum, hB, hraw⟩
  dsimp only at hB hraw
  apply row_decomposition_tiers r (fun i => rowResidual n g (W i) (a i) (D i) (tap i))
    n b denom plane line _ hsum
  · simpa only [rowResidual] using hraw
  · intro i
    have := (hmeta i).2.2.2.1
    omega
  · intro i
    simpa only [rowResidual] using hB i
  · exact hsmall
  · intro i hr
    have hm := hmeta i
    have hc : costGates (D i).gates = 0 := by omega
    exact hfull (W i) (a i) (D i) (tap i) (hm.1.trans hr) hm.2.2.1 hc
      hm.2.2.2.2.1 hm.2.2.2.2.2
  · intro i hr
    have hm := hmeta i
    have hc : costGates (D i).gates ≤ 1 := by omega
    exact hone (W i) (a i) (D i) (tap i) (by omega) hm.2.2.1 hc
      hm.2.2.2.2.1 hm.2.2.2.2.2




open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

lemma full_row_cap_of_flat_bound (n b denom plane : ℕ)
    (g : (Fin n → F2) → F2)
    (hflat : ∀ (B : (Fin b → F2) →ₗ[F2] (Fin n → F2))
        (a : Fin n → F2) (q : (Fin b → F2) → F2),
      Function.Injective B → isQuad q →
      denom * (∑ v : Fin b → F2, if g (a + B v) = q v then (1 : ℤ) else -1).natAbs ≤
        2 ^ b * plane)
    (W : Submodule F2 (Fin n → F2)) (a : Fin n → F2)
    (D : Circuit) (tap : Fin n → ℕ)
    (hdimW : Module.finrank F2 W = b)
    (hleg : legalGates n D.gates) (hcost0 : costGates D.gates = 0)
    (hout : D.output < n + D.size) (htap : ∀ j, tap j < n + D.size) :
    denom * rowResidual n g W a D tap ≤ 2 ^ b * plane := by
  classical
  have haff := cost_zero_affine D.gates hleg hcost0
  obtain ⟨d_out, c_out, hd_out⟩ := haff D.output hout
  let pos := fun (y : Fin n → F2) (j : Fin n) =>
    if (D.wires (bitsOf n y)).getD (tap j) false then (1 : F2) else 0
  have htap_aff : ∀ j : Fin n, ∃ (lin : Fin n → F2) (c : F2), ∀ y : Fin n → F2,
      pos y j = dotProduct lin y + c := by
    intro j
    obtain ⟨lin, c, hlin⟩ := haff (tap j) (htap j)
    refine ⟨lin, c, fun y => ?_⟩
    dsimp only [pos]
    change (if (wiresOf D.gates (bitsOf n y)).getD (tap j) false then (1 : F2) else 0) = _
    rw [hlin y, zmod2_decide_bool]
  choose L_tap c_tap hL_tap using htap_aff
  let e : (Fin b → F2) ≃ₗ[F2] W :=
    LinearEquiv.ofFinrankEq (Fin b → F2) W (by rw [Module.finrank_fin_fun, hdimW])
  let B : (Fin b → F2) →ₗ[F2] (Fin n → F2) := W.subtype.comp e.toLinearMap
  have hB_inj : Function.Injective B := Subtype.val_injective.comp e.injective
  let Q : (Fin n → F2) → F2 := fun y =>
    (dotProduct d_out y + c_out) + ∑ j : Fin n, (dotProduct (L_tap j) y + c_tap j) * y j
  let q : (Fin b → F2) → F2 := fun v => Q (a + B v)
  have hq_quad : isQuad q := by
    obtain ⟨u0, b0, hu0⟩ := linear_comp_affine B a d_out c_out
    have hq0 : isQuad (fun v => dotProduct d_out (a + B v) + c_out) := by
      have : (fun v => dotProduct d_out (a + B v) + c_out) = (fun v => dotProduct u0 v + b0) :=
        funext hu0
      rw [this]; exact isQuad_affine u0 b0
    have hq_sum : isQuad (fun v => ∑ j : Fin n, (dotProduct (L_tap j) (a + B v) + c_tap j) * (a + B v) j) := by
      apply isQuad_finset_sum Finset.univ
      intro j _
      obtain ⟨u1, b1, hu1⟩ := linear_comp_affine B a (L_tap j) (c_tap j)
      obtain ⟨u2, b2, hu2⟩ := linear_comp_affine B a (Pi.single j 1) 0
      have hprod : (fun v => (dotProduct (L_tap j) (a + B v) + c_tap j) * (a + B v) j) =
          (fun v => (dotProduct u1 v + b1) * (dotProduct u2 v + b2)) := by
        funext v
        have hcoord : (a + B v) j = dotProduct u2 v + b2 := by
          have := hu2 v
          simpa [single_dotProduct] using this
        rw [hu1 v, hcoord]
      rw [hprod]
      exact isQuad_mul_affine u1 u2 b1 b2
    exact isQuad_add hq0 hq_sum
  have hBval_eq : rowResidual n g W a D tap =
      (∑ v : Fin b → F2, if g (a + B v) = q v then (1 : ℤ) else -1).natAbs := by
    dsimp only [rowResidual]
    congr 1
    rw [← Finset.sum_filter]
    let f_inj : (Fin b → F2) → (Fin n → F2) := fun v => a + B v
    have hbij : Finset.univ.image f_inj = Finset.univ.filter (fun y : Fin n → F2 => y - a ∈ W) := by
      ext y
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter, f_inj]
      constructor
      · rintro ⟨v, rfl⟩
        have : a + B v - a = (e v).val := by
          show a + (e v).val - a = (e v).val; abel
        rw [this]; exact (e v).property
      · intro hy
        refine ⟨e.symm ⟨y - a, hy⟩, ?_⟩
        show a + (e (e.symm ⟨y - a, hy⟩)).val = y
        rw [LinearEquiv.apply_symm_apply]
        exact add_sub_cancel a y
    rw [← hbij, Finset.sum_image (fun v1 _ v2 _ h => hB_inj (add_left_cancel h))]
    refine Finset.sum_congr rfl fun v _ => ?_
    have hDeval : D.eval (bitsOf n (f_inj v)) = decide (dotProduct d_out (f_inj v) + c_out = 1) :=
      hd_out (f_inj v)
    have hdotp : dotProduct (pos (f_inj v)) (f_inj v) =
        ∑ j : Fin n, (dotProduct (L_tap j) (f_inj v) + c_tap j) * (f_inj v) j := by
      simp only [dotProduct, hL_tap]
    change signBool (Bool.xor (D.eval (bitsOf n (f_inj v)))
      (decide (dotProduct (pos (f_inj v)) (f_inj v) = 1))) *
      signBool (decide (g (f_inj v) = 1)) = _
    rw [hDeval, hdotp, ← zmod2_add_decide]
    change signBool (decide (q v = 1)) * signBool (decide (g (a + B v) = 1)) = _
    rw [eq_f2_sign, mul_comm]
  rw [hBval_eq]
  exact hflat B a q hB_inj hq_quad


end PEqualNP.Outside.L_meta_32057_aux

namespace PEqualNP.Outside.L_meta_32057_aux

lemma isQuad_comp_affine_map {n s : ℕ} {Q : (Fin n → F2) → F2}
    (hQ : isQuad Q) (B : (Fin s → F2) →ₗ[F2] (Fin n → F2))
    (a : Fin n → F2) : isQuad (fun x => Q (a + B x)) := by
  classical
  rcases hQ with ⟨z, l, M, hQ⟩
  have hhead : isQuad (fun x => z + dotProduct l (a + B x)) := by
    obtain ⟨u, c, hu⟩ := linear_comp_affine B a l z
    have heq : (fun x => z + dotProduct l (a + B x)) =
        (fun x => dotProduct u x + c) := by
      funext x
      rw [add_comm]
      exact hu x
    rw [heq]
    exact isQuad_affine u c
  have hsum : isQuad (fun x => ∑ i : Fin n, ∑ j : Fin n,
      M i j * (a + B x) i * (a + B x) j) := by
    apply isQuad_finset_sum Finset.univ
    intro i _
    apply isQuad_finset_sum Finset.univ
    intro j _
    obtain ⟨u1, c1, hu1⟩ := linear_comp_affine B a (M i j • Pi.single i 1) 0
    obtain ⟨u2, c2, hu2⟩ := linear_comp_affine B a (Pi.single j 1) 0
    have heq : (fun x => M i j * (a + B x) i * (a + B x) j) =
        (fun x => (dotProduct u1 x + c1) * (dotProduct u2 x + c2)) := by
      funext x
      rw [← hu1 x, ← hu2 x]
      simp [smul_dotProduct, single_dotProduct, mul_add]
    rw [heq]
    exact isQuad_mul_affine u1 u2 c1 c2
  have heq : (fun x => Q (a + B x)) =
      (fun x => (z + dotProduct l (a + B x)) +
        ∑ i : Fin n, ∑ j : Fin n, M i j * (a + B x) i * (a + B x) j) :=
    funext (fun x => hQ (a + B x))
  rw [heq]
  exact isQuad_add hhead hsum

end PEqualNP.Outside.L_meta_32057_aux
namespace PEqualNP.Outside.L_meta_32057_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

lemma row_xor_field (b : Bool) (x : F2) :
    Bool.xor b (decide (x = 1)) =
      decide ((if b then (1 : F2) else 0) + x = 1) := by
  cases b <;> fin_cases x <;> decide

lemma one_row_cap_of_cubic_flat_bound (n s denom bound : ℕ)
    (g : (Fin n → F2) → F2)
    (hflat : ∀ (B : (Fin s → F2) →ₗ[F2] (Fin n → F2))
        (a : Fin n → F2) (q : (Fin s → F2) → F2)
        (u v t : Fin s → F2) (α β γ : F2),
      Function.Injective B → isQuad q →
      denom * (∑ x : Fin s → F2, if g (a + B x) =
        q x + (dotProduct u x + α) * (dotProduct v x + β) * (dotProduct t x + γ)
        then (1 : ℤ) else -1).natAbs ≤ bound)
    (W : Submodule F2 (Fin n → F2)) (a : Fin n → F2)
    (D : Circuit) (tap : Fin n → ℕ)
    (hdimW : Module.finrank F2 W = s)
    (hleg : legalGates n D.gates) (hcost : costGates D.gates ≤ 1)
    (hout : D.output < n + D.size) (htap : ∀ j, tap j < n + D.size) :
    denom * rowResidual n g W a D tap ≤ bound := by
  classical
  obtain ⟨u, v, t, α, β, γ, Q, hQ, hphase⟩ :=
    cost_one_phase D hleg hcost hout tap htap
  let e : (Fin s → F2) ≃ₗ[F2] W :=
    LinearEquiv.ofFinrankEq (Fin s → F2) W (by rw [Module.finrank_fin_fun, hdimW])
  let B : (Fin s → F2) →ₗ[F2] (Fin n → F2) := W.subtype.comp e.toLinearMap
  have hB : Function.Injective B := Subtype.val_injective.comp e.injective
  obtain ⟨u', α', hu⟩ := linear_comp_affine B a u α
  obtain ⟨v', β', hv⟩ := linear_comp_affine B a v β
  obtain ⟨t', γ', ht⟩ := linear_comp_affine B a t γ
  let q : (Fin s → F2) → F2 := fun x => Q (a + B x)
  have hq : isQuad q := isQuad_comp_affine_map hQ B a
  have heq : rowResidual n g W a D tap =
      (∑ x : Fin s → F2, if g (a + B x) =
        q x + (dotProduct u' x + α') * (dotProduct v' x + β') * (dotProduct t' x + γ')
        then (1 : ℤ) else -1).natAbs := by
    dsimp only [rowResidual]
    congr 1
    rw [← Finset.sum_filter]
    let f : (Fin s → F2) → (Fin n → F2) := fun x => a + B x
    have hbij : Finset.univ.image f =
        Finset.univ.filter (fun y : Fin n → F2 => y - a ∈ W) := by
      ext y
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter, f]
      constructor
      · rintro ⟨x, rfl⟩
        have hx : a + B x - a = (e x).val := by
          show a + (e x).val - a = (e x).val
          abel
        rw [hx]
        exact (e x).property
      · intro hy
        refine ⟨e.symm ⟨y - a, hy⟩, ?_⟩
        show a + (e (e.symm ⟨y - a, hy⟩)).val = y
        rw [LinearEquiv.apply_symm_apply]
        exact add_sub_cancel a y
    rw [← hbij, Finset.sum_image (fun x _ y _ h => hB (add_left_cancel h))]
    apply Finset.sum_congr rfl
    intro x hx
    rw [row_xor_field, hphase]
    change signBool (decide ((Q (a + B x) +
      (dotProduct u (a + B x) + α) * (dotProduct v (a + B x) + β) *
        (dotProduct t (a + B x) + γ)) = 1)) * signBool (decide (g (a + B x) = 1)) = _
    rw [hu x, hv x, ht x, eq_f2_sign, mul_comm]
  rw [heq]
  exact hflat B a q u' v' t' α' β' γ' hB hq

end PEqualNP.Outside.L_meta_32057_aux

namespace PEqualNP.Outside.L_meta_32057_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

lemma raw_bound_from_two_flat_caps (n b denom plane line : ℕ)
    (g : (Fin n → F2) → F2)
    (hsmall : denom ≤ 4 * max plane line)
    (hflat : ∀ (B : (Fin b → F2) →ₗ[F2] (Fin n → F2))
        (a : Fin n → F2) (q : (Fin b → F2) → F2),
      Function.Injective B → isQuad q →
      denom * (∑ x : Fin b → F2, if g (a + B x) = q x then (1 : ℤ) else -1).natAbs ≤
        2 ^ b * plane)
    (hcubic : ∀ (B : (Fin (b - 1) → F2) →ₗ[F2] (Fin n → F2))
        (a : Fin n → F2) (q : (Fin (b - 1) → F2) → F2)
        (u v t : Fin (b - 1) → F2) (α β γ : F2),
      Function.Injective B → isQuad q →
      denom * (∑ x : Fin (b - 1) → F2, if g (a + B x) =
        q x + (dotProduct u x + α) * (dotProduct v x + β) * (dotProduct t x + γ)
        then (1 : ℤ) else -1).natAbs ≤ 2 ^ b * line)
    (C : Circuit) (hleg : legalGates (2 * n) C.gates) (hcost : costGates C.gates ≤ b) :
    denom * (∑ x : Fin n → F2, ∑ y : Fin n → F2,
      if C.eval (bitsOf n x ++ bitsOf n y) = decide (dotProduct x y + g y = 1)
      then (1 : ℤ) else -1).natAbs ≤ 2 ^ (n + b) * max plane line := by
  apply row_raw_bound_of_tiers n b denom plane line g hsmall
  · exact full_row_cap_of_flat_bound n b denom plane g hflat
  · intro W a D tap hdim hlegal hcost hout htap
    apply one_row_cap_of_cubic_flat_bound n (b - 1) denom (2 ^ b * line) g
      hcubic W a D tap (by omega) hlegal hcost hout htap
  · exact hleg
  · exact hcost

end PEqualNP.Outside.L_meta_32057_aux

namespace PEqualNP.Outside.L_meta_32057_aux

lemma exact_gap_circuit_bound : ∀ (k m r d : ℕ), 2 ≤ k → 0 < d →
  let n := k+2*m+r
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let F := ZMod 2
  let legal := fun (width : ℕ) (C : Circ) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack width C ∧
      (∀ h ∈ C.gates, h.inputs.length ≤ 2 ∧
        (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1)))
  let cost := fun (C : Circ) => C.gates.countP (fun h => @decide
    ((h.op = .and ∨ h.op = .or) ∧ h.inputs.length = 2) (Classical.propDecidable _))
  let bits := fun (width : ℕ) (u : Fin width → F) => List.ofFn (fun j : Fin width => decide (u j = 1))
  let V := Fin n → F
  let S := Fin k → F
  let D := Fin m → F
  let Z := Fin r → F
  let base := 2*m+r
  ∀ (e : V ≃ₗ[F] S × (D × (D × Z))) (A : Fin m → S),
    let wt := fun (a : S) => ((Finset.univ : Finset (Fin m)).filter
      (fun i => dotProduct (A i) a ≠ 0)).card
    (∀ a : S, a ≠ 0 → d ≤ wt a) → (∃ a : S, a ≠ 0 ∧ wt a = d) →
    ∀ h : S → F,
      let g := fun (y : V) => h (e y).1 + ∑ i : Fin m,
        dotProduct (A i) (e y).1 * (e y).2.1 i * (e y).2.2.1 i
      let raw := fun (C : Circ) => (∑ x : V, ∑ y : V,
        if C.eval (bits n x ++ bits n y) = decide (dotProduct x y + g y = 1)
        then (1 : ℤ) else -1).natAbs
      let b := base+2
      let E := Fin b → F
      let quad := fun (q : E → F) => ∃ (z : F) (l : E) (M : Fin b → Fin b → F),
        ∀ x, q x = z + dotProduct l x + ∑ i, ∑ j, M i j * x i * x j
      let flat := fun (L : E →ₗ[F] V) (a : V) (q : E → F) =>
        (∑ x : E, if g (a+L x) = q x then (1 : ℤ) else -1).natAbs
      let mass := fun (w : S × S) =>
        if w.1 ≠ 0 ∧ w.2 ≠ 0 ∧ w.1 ≠ w.2 then
          2^m + 2^(m-wt w.1) + 2^(m-wt w.2) + 2^(m-wt (w.1+w.2)) else 0
      let plane := (Finset.univ : Finset (S × S)).sup mass
      let line := 2^m + 2^(m+1-d)
      let denom := 2^(m+2)
      (∀ (L : E →ₗ[F] V) (a : V) (q : E → F), Function.Injective L → quad q →
        denom * flat L a q ≤ 2^b * plane) →
      (∀ (L : (Fin (b-1) → F) →ₗ[F] V) (a : V)
          (q : (Fin (b-1) → F) → F) (u v t : Fin (b-1) → F) (α β γ : F),
        Function.Injective L →
        (∃ (z : F) (l : Fin (b-1) → F) (M : Fin (b-1) → Fin (b-1) → F),
          ∀ x, q x = z + dotProduct l x + ∑ i, ∑ j, M i j * x i * x j) →
        denom * (∑ x : Fin (b-1) → F, if g (a+L x) =
          q x + (dotProduct u x + α) * (dotProduct v x + β) * (dotProduct t x + γ)
          then (1 : ℤ) else -1).natAbs ≤ 2^b * line) →
      (∀ C : Circ, legal (2*n) C → cost C ≤ b →
        denom * raw C ≤ 2^(n+b) * max plane line) := by
  intro k m r d hk hd n Circ F legal cost bits V S D Z base e A wt hmin hword h
  intro g raw b E quad flat mass plane line denom hflat hcubic
  have hline : 2 ^ m ≤ line := Nat.le_add_right _ _
  have hsmall : denom ≤ 4 * max plane line := by
    calc
      denom = 4 * 2 ^ m := by dsimp only [denom]; rw [Nat.pow_add]; ring
      _ ≤ 4 * max plane line := Nat.mul_le_mul_left _ (hline.trans (le_max_right _ _))
  exact raw_bound_from_two_flat_caps n b denom plane line g hsmall hflat hcubic

end PEqualNP.Outside.L_meta_32057_aux

namespace PEqualNP.Outside.L_meta_32057_aux


def rowDotLinear {n : ℕ} (u : Fin n → F2) : (Fin n → F2) →ₗ[F2] F2 where
  toFun x := dotProduct u x
  map_add' x y := dotProduct_add u x y
  map_smul' c x := by simp only [dotProduct_smul, RingHom.id_apply]

def rowDotAffine {n : ℕ} (u : Fin n → F2) (c : F2) :
    (Fin n → F2) →ᵃ[F2] F2 :=
  (rowDotLinear u).toAffineMap + AffineMap.const F2 (Fin n → F2) c

lemma rowDotAffine_apply {n : ℕ} (u : Fin n → F2) (c : F2) (x : Fin n → F2) :
    rowDotAffine u c x = dotProduct u x + c := rfl

end PEqualNP.Outside.L_meta_32057_aux
namespace PEqualNP.Outside.L_meta_32057_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

lemma one_row_cap_of_affine_map_flat_bound (n s denom bound : ℕ)
    (g : (Fin n → F2) → F2)
    (hflat : ∀ (B : (Fin s → F2) →ₗ[F2] (Fin n → F2))
        (a : Fin n → F2) (q : (Fin s → F2) → F2)
        (u v t : (Fin s → F2) →ᵃ[F2] F2),
      Function.Injective B → isQuad q →
      denom * (∑ x : Fin s → F2, if g (a + B x) =
        q x + u x * v x * t x then (1 : ℤ) else -1).natAbs ≤ bound)
    (W : Submodule F2 (Fin n → F2)) (a : Fin n → F2)
    (D : Circuit) (tap : Fin n → ℕ)
    (hdimW : Module.finrank F2 W = s)
    (hleg : legalGates n D.gates) (hcost : costGates D.gates ≤ 1)
    (hout : D.output < n + D.size) (htap : ∀ j, tap j < n + D.size) :
    denom * rowResidual n g W a D tap ≤ bound := by
  apply one_row_cap_of_cubic_flat_bound n s denom bound g _ W a D tap hdimW hleg hcost hout htap
  intro B a q u v t α β γ hB hq
  exact hflat B a q (rowDotAffine u α) (rowDotAffine v β) (rowDotAffine t γ) hB hq

end PEqualNP.Outside.L_meta_32057_aux

theorem PEqualNP.Outside.L_meta_32057 :
∀ (k m r d : ℕ), 2 ≤ k → 0 < d →
  let n := k+2*m+r
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let F := ZMod 2
  let legal := fun (width : ℕ) (C : Circ) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack width C ∧
      (∀ h ∈ C.gates, h.inputs.length ≤ 2 ∧
        (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1)))
  let cost := fun (C : Circ) => C.gates.countP (fun h => @decide
    ((h.op = .and ∨ h.op = .or) ∧ h.inputs.length = 2) (Classical.propDecidable _))
  let bits := fun (width : ℕ) (u : Fin width → F) => List.ofFn (fun j : Fin width => decide (u j = 1))
  let V := Fin n → F
  let S := Fin k → F
  let D := Fin m → F
  let Z := Fin r → F
  let base := 2*m+r
  ∀ (e : V ≃ₗ[F] S × (D × (D × Z))) (A : Fin m → S),
    let wt := fun (a : S) => ((Finset.univ : Finset (Fin m)).filter
      (fun i => dotProduct (A i) a ≠ 0)).card
    (∀ a : S, a ≠ 0 → d ≤ wt a) → (∃ a : S, a ≠ 0 ∧ wt a = d) →
    ∀ h : S → F,
      let g := fun (y : V) => h (e y).1 + ∑ i : Fin m,
        dotProduct (A i) (e y).1 * (e y).2.1 i * (e y).2.2.1 i
      let raw := fun (C : Circ) => (∑ x : V, ∑ y : V,
        if C.eval (bits n x ++ bits n y) = decide (dotProduct x y + g y = 1)
        then (1 : ℤ) else -1).natAbs
      let b := base+2
      let E := Fin b → F
      let quad := fun (q : E → F) => ∃ (z : F) (l : E) (M : Fin b → Fin b → F),
        ∀ x, q x = z + dotProduct l x + ∑ i, ∑ j, M i j * x i * x j
      let flat := fun (L : E →ₗ[F] V) (a : V) (q : E → F) =>
        (∑ x : E, if g (a+L x) = q x then (1 : ℤ) else -1).natAbs
      let mass := fun (w : S × S) =>
        if w.1 ≠ 0 ∧ w.2 ≠ 0 ∧ w.1 ≠ w.2 then
          2^m + 2^(m-wt w.1) + 2^(m-wt w.2) + 2^(m-wt (w.1+w.2)) else 0
      let plane := (Finset.univ : Finset (S × S)).sup mass
      let line := 2^m + 2^(m+1-d)
      let denom := 2^(m+2)
      (∀ (L : E →ₗ[F] V) (a : V) (q : E → F), Function.Injective L → quad q →
        denom * flat L a q ≤ 2^b * plane) ∧
      (∃ (L : E →ₗ[F] V) (a : V) (q : E → F), Function.Injective L ∧ quad q ∧
        denom * flat L a q = 2^b * plane) ∧
      (∀ C : Circ, legal (2*n) C → cost C ≤ b →
        denom * raw C ≤ 2^(n+b) * max plane line) ∧
      (∃ C : Circ, legal (2*n) C ∧ cost C ≤ b ∧
        denom * raw C = 2^(n+b) * max plane line) := by
  intro k m r d hk hd
  dsimp only
  intro e A hmin hword h
  have hdm : d ≤ m := by
    obtain ⟨a, ha, hw⟩ := hword
    rw [← hw]
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hflat := PEqualNP.Outside.L_meta_32057_aux.original_flat_upper_of_terminal
    k m r e A h (PEqualNP.Outside.L_meta_32057_aux.terminal_flat_oracle_proved _ _ _)
  have hlineflat := PEqualNP.Outside.L_meta_32057_aux.original_line_upper_of_terminal
    k m r d hd hdm e A h hmin
    (PEqualNP.Outside.L_meta_32057_aux.terminal_line_oracle _ d hd)
  have hupper := PEqualNP.Outside.L_meta_32057_aux.exact_gap_circuit_bound
    k m r d hk hd e A hmin hword h hflat (by
      intro L a q u v t α β γ hL hq
      exact hlineflat L a q
        (PEqualNP.Outside.L_meta_32057_aux.rowDotAffine u α)
        (PEqualNP.Outside.L_meta_32057_aux.rowDotAffine v β)
        (PEqualNP.Outside.L_meta_32057_aux.rowDotAffine t γ) hL hq)
  refine ⟨hflat, ?_, hupper, ?_⟩
  · exact PEqualNP.Outside.L_meta_32057_aux.plane_attainment k m r hk e A h
  · refine PEqualNP.Outside.L_meta_32057_aux.circuit_attainment_from_plane_and_line
      (k + 2 * m + r) (2 * m + r + 2) (2 ^ (m + 2)) _ _ _ hupper ?_ ?_
    · exact PEqualNP.Outside.L_meta_32057_aux.plane_attainment k m r hk e A h
    · obtain ⟨C, hleg, hcost, hraw⟩ :=
        PEqualNP.Outside.L_meta_32057_aux.LineAttainment.circuit_line_attainment
          hd e A h hword
      exact ⟨C, hleg, le_of_eq hcost, le_of_eq hraw.symm⟩
