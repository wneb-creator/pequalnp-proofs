import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_226

open Module

theorem one_ne0 : (1 : ZMod 5) ≠ 0 := by decide
theorem two_ne0 : (2 : ZMod 5) ≠ 0 := by decide
theorem three_ne0 : (3 : ZMod 5) ≠ 0 := by decide
theorem six_eq1 : (6 : ZMod 5) = 1 := by decide
theorem six_ne0 : (6 : ZMod 5) ≠ 0 := by decide
theorem six_sub_six : (6 : ZMod 5) - 3 * 6 + 3 * 6 - 6 = 0 := by decide

section WithFact

variable [Fact (Nat.Prime 5)]

theorem orth_bound {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Submodule (ZMod 5) (ι → (ZMod 5)))
    (h : ∀ a ∈ A, ∀ b ∈ B, dotProduct a b = 0) :
    finrank (ZMod 5) A + finrank (ZMod 5) B ≤ Fintype.card ι := by
  set W : Submodule (ZMod 5) (Module.Dual (ZMod 5) (ι → (ZMod 5))) := A.map (dotProductEquiv (ZMod 5) ι).toLinearMap with hW
  have hWrank : finrank (ZMod 5) W = finrank (ZMod 5) A := LinearEquiv.finrank_map_eq (dotProductEquiv (ZMod 5) ι) A
  have hsum := Subspace.finrank_add_finrank_dualCoannihilator_eq W
  rw [hWrank, Module.finrank_fintype_fun_eq_card] at hsum
  have hle : B ≤ W.dualCoannihilator := by
    intro x hx
    rw [Submodule.mem_dualCoannihilator]
    intro φ hφ
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.1 hφ
    simpa [dotProductEquiv] using h a ha x hx
  have := Submodule.finrank_mono hle
  omega

theorem rank_nullity {V W : Type} [AddCommGroup V] [Module (ZMod 5) V] [FiniteDimensional (ZMod 5) V]
    [AddCommGroup W] [Module (ZMod 5) W] (K : Submodule (ZMod 5) V) (p : V →ₗ[(ZMod 5)] W) :
    finrank (ZMod 5) (K.map p) + finrank (ZMod 5) ↥(K ⊓ LinearMap.ker p) = finrank (ZMod 5) K := by
  have h := LinearMap.finrank_range_add_finrank_ker (p.domRestrict K)
  rw [LinearMap.range_domRestrict] at h
  have h2 : (LinearMap.ker (p.domRestrict K)).map K.subtype = K ⊓ LinearMap.ker p := by
    rw [LinearMap.ker_domRestrict, Submodule.map_comap_subtype]
  have h3 : finrank (ZMod 5) ((LinearMap.ker (p.domRestrict K)).map K.subtype) =
      finrank (ZMod 5) (LinearMap.ker (p.domRestrict K)) :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ K.injective_subtype _)).symm
  rw [h2] at h3
  omega

theorem finrank_sup_span {V : Type} [AddCommGroup V] [Module (ZMod 5) V] [FiniteDimensional (ZMod 5) V]
    (L : Submodule (ZMod 5) V) (x : V) (hx : x ∉ L) :
    finrank (ZMod 5) ↥(L ⊔ Submodule.span (ZMod 5) {x}) = finrank (ZMod 5) L + 1 := by
  have hinf : L ⊓ Submodule.span (ZMod 5) {x} = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨hvL, hvS⟩ := Submodule.mem_inf.1 hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hvS
    by_cases hc : c = 0
    · simp [hc]
    · exact absurd ((L.smul_mem_iff hc).1 hvL) hx
  have hx0 : x ≠ 0 := by
    intro h; apply hx; rw [h]; exact L.zero_mem
  have := Submodule.finrank_sup_add_finrank_inf_eq L (Submodule.span (ZMod 5) {x})
  rw [hinf, finrank_bot, add_zero, finrank_span_singleton hx0] at this
  exact this

def p2 (M : Fin 2 × Fin 2 → (ZMod 5)) : (ZMod 5) := M (0, 0) * M (1, 1) + M (0, 1) * M (1, 0)

def sw2 : (Fin 2 × Fin 2 → (ZMod 5)) →ₗ[(ZMod 5)] (Fin 2 × Fin 2 → (ZMod 5)) where
  toFun y := fun q => y (Fin.rev q.1, Fin.rev q.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem p2_add (X y : Fin 2 × Fin 2 → (ZMod 5)) :
    p2 (X + y) = p2 X + p2 y + dotProduct X (sw2 y) := by
  simp [p2, sw2, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

theorem sw2_inj : Function.Injective sw2 := by
  intro a b h
  funext q
  have := congrFun h (Fin.rev q.1, Fin.rev q.2)
  simpa [sw2] using this

theorem F2 (L : Submodule (ZMod 5) (Fin 2 × Fin 2 → (ZMod 5))) (X0 : Fin 2 × Fin 2 → (ZMod 5))
    (hinv : ∀ X ∈ L ⊔ Submodule.span (ZMod 5) {X0}, ∀ y ∈ L, p2 (X + y) = p2 X) (hne : p2 X0 ≠ 0) :
    finrank (ZMod 5) L ≤ 1 := by
  have hz : ∀ y ∈ L, p2 y = 0 := by
    intro y hy
    have := hinv 0 (Submodule.zero_mem _) y hy
    rw [zero_add] at this
    rw [this]; simp [p2]
  have hX0 : X0 ∉ L := fun h => hne (hz X0 h)
  have hdot : ∀ a ∈ L.map sw2, ∀ b ∈ L ⊔ Submodule.span (ZMod 5) {X0}, dotProduct a b = 0 := by
    intro a ha b hb
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 ha
    have e := p2_add b y
    rw [hinv b hb y hy, hz y hy] at e
    rw [dotProduct_comm]
    linear_combination -e
  have h1 := orth_bound _ _ hdot
  have h2 : finrank (ZMod 5) (L.map sw2) = finrank (ZMod 5) L :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ sw2_inj L)).symm
  have h3 := finrank_sup_span L X0 hX0
  simp only [Fintype.card_prod, Fintype.card_fin] at h1
  omega


def p3 (M : Fin 3 × Fin 3 → (ZMod 5)) : (ZMod 5) :=
  M (0, 0) * M (1, 1) * M (2, 2) + M (0, 0) * M (1, 2) * M (2, 1) +
  M (0, 1) * M (1, 0) * M (2, 2) + M (0, 1) * M (1, 2) * M (2, 0) +
  M (0, 2) * M (1, 0) * M (2, 1) + M (0, 2) * M (1, 1) * M (2, 0)

def mn3 : (Fin 3 × Fin 3 → (ZMod 5)) →ₗ[(ZMod 5)] (Fin 2 × Fin 2 → (ZMod 5)) where
  toFun X := fun q => X (q.1.succ, q.2.succ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def row3 : (Fin 3 × Fin 3 → (ZMod 5)) →ₗ[(ZMod 5)] (Fin 3 → (ZMod 5)) where
  toFun X := fun k => X (0, k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem p3_smul (c : (ZMod 5)) (M : Fin 3 × Fin 3 → (ZMod 5)) : p3 (c • M) = c ^ 3 * p3 M := by
  simp [p3]; ring

theorem p3_lap (M : Fin 3 × Fin 3 → (ZMod 5)) (h1 : M (0, 1) = 0) (h2 : M (0, 2) = 0) :
    p3 M = M (0, 0) * p2 (mn3 M) := by
  simp [p3, p2, mn3, h1, h2]; ring

theorem p2_interp (A B : Fin 2 × Fin 2 → (ZMod 5)) :
    p2 A = 3 * p2 (A + (1 : (ZMod 5)) • B) - 3 * p2 (A + (2 : (ZMod 5)) • B) + p2 (A + (3 : (ZMod 5)) • B) := by
  simp [p2]; ring

theorem F3_core (L : Submodule (ZMod 5) (Fin 3 × Fin 3 → (ZMod 5))) (X0 : Fin 3 × Fin 3 → (ZMod 5))
    (hinv : ∀ X ∈ L ⊔ Submodule.span (ZMod 5) {X0}, ∀ y ∈ L, p3 (X + y) = p3 X)
    (Xs : Fin 3 × Fin 3 → (ZMod 5)) (hXsC : Xs ∈ L ⊔ Submodule.span (ZMod 5) {X0})
    (hXs0 : Xs (0, 0) = 1) (hXs1 : Xs (0, 1) = 0) (hXs2 : Xs (0, 2) = 0) (hXsne : p3 Xs ≠ 0)
    (W1 : Fin 3 × Fin 3 → (ZMod 5)) (hW1C : W1 ∈ L ⊔ Submodule.span (ZMod 5) {X0})
    (hW11 : W1 (0, 1) = 1) (hW12 : W1 (0, 2) = 0)
    (W2 : Fin 3 × Fin 3 → (ZMod 5)) (hW2C : W2 ∈ L ⊔ Submodule.span (ZMod 5) {X0})
    (hW21 : W2 (0, 1) = 0) (hW22 : W2 (0, 2) = 1) :
    Module.finrank (ZMod 5) L ≤ 3 := by
  set C := L ⊔ Submodule.span (ZMod 5) {X0} with hC
  have hLC : L ≤ C := le_sup_left
  by_contra hcon
  push Not at hcon
  set K := L ⊓ LinearMap.ker row3 with hK
  have hrowL : Module.finrank (ZMod 5) (L.map row3) ≤ 2 := by
    have hne : L.map row3 ≠ ⊤ := by
      intro htop
      have : (Pi.single 0 1 : Fin 3 → (ZMod 5)) ∈ L.map row3 := by rw [htop]; trivial
      obtain ⟨y, hy, hyr⟩ := Submodule.mem_map.1 this
      have e := hinv Xs hXsC (-y) (L.neg_mem hy)
      have h0 : p3 (Xs + -y) = 0 := by
        have r0 := congrFun hyr 0
        have r1 := congrFun hyr 1
        have r2 := congrFun hyr 2
        simp [row3] at r0 r1 r2
        simp [p3, r0, r1, r2, hXs0, hXs1, hXs2]
      exact hXsne (e ▸ h0)
    have h3 := Submodule.finrank_lt hne
    rw [Module.finrank_fin_fun] at h3
    omega
  have hKdim : Module.finrank (ZMod 5) L ≤ Module.finrank (ZMod 5) K + 2 := by
    have h := rank_nullity L row3
    rw [show L ⊓ LinearMap.ker row3 = K from rfl] at h
    omega
  have KL : ∀ z ∈ K, ∀ c : (ZMod 5), p2 (mn3 z + c • mn3 Xs) = c ^ 2 * p3 Xs := by
    intro z hz c
    have hzL : z ∈ L := (Submodule.mem_inf.1 hz).1
    have hzr : row3 z = 0 := (Submodule.mem_inf.1 hz).2
    have z0 : z (0, 0) = 0 := congrFun hzr 0
    have z1 : z (0, 1) = 0 := congrFun hzr 1
    have z2 : z (0, 2) = 0 := congrFun hzr 2
    have main : ∀ c : (ZMod 5), c ≠ 0 → p2 (mn3 z + c • mn3 Xs) = c ^ 2 * p3 Xs := by
      intro c hc
      have e := hinv (c • Xs) (C.smul_mem c hXsC) z hzL
      rw [p3_smul] at e
      have e2 := p3_lap (c • Xs + z) (by simp [hXs1, z1]) (by simp [hXs2, z2])
      rw [e] at e2
      have hm : mn3 (c • Xs + z) = mn3 z + c • mn3 Xs := by
        rw [map_add, map_smul, add_comm]
      rw [hm] at e2
      simp [hXs0, z0] at e2
      have : c * (p2 (mn3 z + c • mn3 Xs) - c ^ 2 * p3 Xs) = 0 := by linear_combination -e2
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hc
      · linear_combination h
    by_cases hc : c = 0
    · subst hc
      rw [zero_smul, add_zero, p2_interp (mn3 z) (mn3 Xs), main 1 one_ne0,
        main 2 two_ne0, main 3 three_ne0]
      ring
    · exact main c hc
  set L2 := K.map mn3 with hL2
  have hF2 : Module.finrank (ZMod 5) L2 ≤ 1 := by
    apply F2 L2 (mn3 Xs)
    · intro M hM m hm
      obtain ⟨m1, hm1, M', hM', rfl⟩ := Submodule.mem_sup.1 hM
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hM'
      obtain ⟨z1, hz1, rfl⟩ := Submodule.mem_map.1 hm1
      obtain ⟨z2, hz2, rfl⟩ := Submodule.mem_map.1 hm
      have e1 := KL z1 hz1 c
      have e2 := KL (z1 + z2) (K.add_mem hz1 hz2) c
      rw [map_add] at e2
      rw [show mn3 z1 + c • mn3 Xs + mn3 z2 = mn3 z1 + mn3 z2 + c • mn3 Xs by abel, e2, e1]
    · have h := KL 0 K.zero_mem 1
      rw [map_zero, zero_add, one_smul, one_pow, one_mul] at h
      rw [h]; exact hXsne

  set Z := K ⊓ LinearMap.ker mn3 with hZ
  have hZdim : Module.finrank (ZMod 5) K = Module.finrank (ZMod 5) L2 + Module.finrank (ZMod 5) Z := by
    have h := rank_nullity K mn3
    rw [show K ⊓ LinearMap.ker mn3 = Z from rfl, show K.map mn3 = L2 from rfl] at h
    omega
  have hZe : ∀ z ∈ Z, z (0, 0) = 0 ∧ z (0, 1) = 0 ∧ z (0, 2) = 0 ∧ z (1, 1) = 0 ∧
      z (1, 2) = 0 ∧ z (2, 1) = 0 ∧ z (2, 2) = 0 := by
    intro z hz
    have hzK := (Submodule.mem_inf.1 hz).1
    have hzr : row3 z = 0 := (Submodule.mem_inf.1 hzK).2
    have hzm : mn3 z = 0 := (Submodule.mem_inf.1 hz).2
    refine ⟨congrFun hzr 0, congrFun hzr 1, congrFun hzr 2, congrFun hzm (0, 0),
      congrFun hzm (0, 1), congrFun hzm (1, 0), congrFun hzm (1, 1)⟩
  have hPhi : ∀ z ∈ Z, ∀ X1 ∈ C, X1 (0, 1) = 0 → X1 (0, 2) = 0 →
      z (1, 0) * X1 (2, 2) + z (2, 0) * X1 (1, 2) = 0 ∧
      z (1, 0) * X1 (2, 1) + z (2, 0) * X1 (1, 1) = 0 := by
    intro z hz X1 hX1 h1 h2
    obtain ⟨e00, e01, e02, e11, e12, e21, e22⟩ := hZe z hz
    have hzL : z ∈ L := (Submodule.mem_inf.1 (Submodule.mem_inf.1 hz).1).1
    have hf : ∀ X ∈ C, z (1, 0) * (X (0, 1) * X (2, 2) + X (0, 2) * X (2, 1)) +
        z (2, 0) * (X (0, 1) * X (1, 2) + X (0, 2) * X (1, 1)) = 0 := by
      intro X hX
      have e := hinv X hX z hzL
      simp only [p3, Pi.add_apply, e00, e01, e02, e11, e12, e21, e22] at e
      linear_combination e
    have fa := hf (X1 + W1) (C.add_mem hX1 hW1C)
    have fb := hf (X1 - W1) (C.sub_mem hX1 hW1C)
    have fc := hf (X1 + W2) (C.add_mem hX1 hW2C)
    have fd := hf (X1 - W2) (C.sub_mem hX1 hW2C)
    simp only [Pi.add_apply, Pi.sub_apply, h1, h2, hW11, hW12, hW21, hW22] at fa fb fc fd
    constructor
    · have hmul : (2 : ZMod 5) * (z (1, 0) * X1 (2, 2) + z (2, 0) * X1 (1, 2)) = 0 := by
        linear_combination fa - fb
      exact (mul_eq_zero.1 hmul).resolve_left two_ne0
    · have hmul : (2 : ZMod 5) * (z (1, 0) * X1 (2, 1) + z (2, 0) * X1 (1, 1)) = 0 := by
        linear_combination fc - fd
      exact (mul_eq_zero.1 hmul).resolve_left two_ne0
  have hP : Xs (1, 1) * Xs (2, 2) + Xs (1, 2) * Xs (2, 1) ≠ 0 := by
    have := p3_lap Xs hXs1 hXs2
    rw [hXs0, one_mul] at this
    rw [this] at hXsne
    simpa [p2, mn3] using hXsne
  have hab : ∀ z ∈ Z, z ≠ 0 → z (1, 0) ≠ 0 ∧ z (2, 0) ≠ 0 := by
    intro z hz hz0
    obtain ⟨e00, e01, e02, e11, e12, e21, e22⟩ := hZe z hz
    obtain ⟨q1, q2⟩ := hPhi z hz Xs hXsC hXs1 hXs2
    have hnz : z (1, 0) ≠ 0 ∨ z (2, 0) ≠ 0 := by
      by_contra hc
      push Not at hc
      apply hz0
      funext q
      obtain ⟨i, k⟩ := q
      fin_cases i <;> fin_cases k
      · exact e00
      · exact e01
      · exact e02
      · exact hc.1
      · exact e11
      · exact e12
      · exact hc.2
      · exact e21
      · exact e22
    constructor
    · intro ha
      have hb : z (2, 0) ≠ 0 := by tauto
      rw [ha, zero_mul, zero_add] at q1 q2
      have h12 : Xs (1, 2) = 0 := (mul_eq_zero.1 q1).resolve_left hb
      have h11 : Xs (1, 1) = 0 := (mul_eq_zero.1 q2).resolve_left hb
      apply hP; rw [h12, h11]; ring
    · intro hb
      have ha : z (1, 0) ≠ 0 := by tauto
      rw [hb, zero_mul, add_zero] at q1 q2
      have h22 : Xs (2, 2) = 0 := (mul_eq_zero.1 q1).resolve_left ha
      have h21 : Xs (2, 1) = 0 := (mul_eq_zero.1 q2).resolve_left ha
      apply hP; rw [h22, h21]; ring
  have hZpos : 1 ≤ Module.finrank (ZMod 5) Z := by omega
  have hZne : Z ≠ ⊥ := by
    intro h; rw [h, finrank_bot] at hZpos; omega
  obtain ⟨z0, hz0Z, hz0⟩ := Submodule.ne_bot_iff _ |>.1 hZne
  obtain ⟨ha, hb⟩ := hab z0 hz0Z hz0
  have hL2bot : ∀ m ∈ L2, m = 0 := by
    intro m hm
    obtain ⟨z', hz', rfl⟩ := Submodule.mem_map.1 hm
    have hz'L : z' ∈ L := (Submodule.mem_inf.1 hz').1
    have hz'r : row3 z' = 0 := (Submodule.mem_inf.1 hz').2
    obtain ⟨q1, q2⟩ := hPhi z0 hz0Z z' (hLC hz'L) (congrFun hz'r 1) (congrFun hz'r 2)
    obtain ⟨s1, s2⟩ := hPhi z0 hz0Z Xs hXsC hXs1 hXs2
    have k0 := KL z' hz' 0
    have k1 := KL z' hz' 1
    simp only [zero_smul, add_zero, one_smul, one_pow, one_mul, zero_pow two_ne_zero,
      zero_mul] at k0 k1
    have hp3 := p3_lap Xs hXs1 hXs2
    rw [hXs0, one_mul] at hp3
    rw [hp3] at k1
    simp only [p2, mn3, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply] at k0 k1
    simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at k0 k1
    set a := z0 (1, 0)
    set b := z0 (2, 0)
    set u := z' (1, 1)
    set v := z' (1, 2)
    set w := z' (2, 1)
    set x := z' (2, 2)
    set U := Xs (1, 1)
    set V := Xs (1, 2)
    set W' := Xs (2, 1)
    set X' := Xs (2, 2)
    have e6 : u * X' + x * U + v * W' + w * V = 0 := by linear_combination k1 - k0
    have huv : b * (u * v) = 0 := by
      have hmul : (2 : ZMod 5) * (b * (u * v)) = 0 := by
        linear_combination -(a * k0 - u * q1 - v * q2)
      exact (mul_eq_zero.1 hmul).resolve_left two_ne0
    have huV : b * (u * V + v * U) = 0 := by
      have hmul : (2 : ZMod 5) * (b * (u * V + v * U)) = 0 := by
        linear_combination -(a * e6 - u * s1 - U * q1 - v * s2 - V * q2)
      exact (mul_eq_zero.1 hmul).resolve_left two_ne0
    have hUV : U * V ≠ 0 := by
      intro h
      apply hP
      have : a * (U * X' + V * W') = -2 * b * (U * V) := by
        linear_combination U * s1 + V * s2
      rw [h, mul_zero] at this
      exact (mul_eq_zero.1 this).resolve_left ha
    have huv' : u * v = 0 := (mul_eq_zero.1 huv).resolve_left hb
    have huV' : u * V + v * U = 0 := (mul_eq_zero.1 huV).resolve_left hb
    have hV : V ≠ 0 := fun h => hUV (by rw [h, mul_zero])
    have hU : U ≠ 0 := fun h => hUV (by rw [h, zero_mul])
    have hu : u = 0 := by
      have : u ^ 2 * V = 0 := by linear_combination u * huV' - U * huv'
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 ((mul_eq_zero.1 this).resolve_right hV)
    have hv : v = 0 := by
      have : v ^ 2 * U = 0 := by linear_combination v * huV' - V * huv'
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 ((mul_eq_zero.1 this).resolve_right hU)
    have hx : x = 0 := by
      have : a * x = 0 := by linear_combination q1 - b * hv
      exact (mul_eq_zero.1 this).resolve_left ha
    have hw : w = 0 := by
      have : a * w = 0 := by linear_combination q2 - b * hu
      exact (mul_eq_zero.1 this).resolve_left ha
    funext q
    obtain ⟨i, k⟩ := q
    fin_cases i <;> fin_cases k
    · exact hu
    · exact hv
    · exact hw
    · exact hx
  have hL20 : Module.finrank (ZMod 5) L2 = 0 := by
    have : L2 = ⊥ := by
      rw [eq_bot_iff]; intro m hm; rw [Submodule.mem_bot]; exact hL2bot m hm
    rw [this, finrank_bot]
  set ev : (Fin 3 × Fin 3 → (ZMod 5)) →ₗ[(ZMod 5)] (ZMod 5) := LinearMap.proj ((1 : Fin 3), (0 : Fin 3)) with hev
  have hev1 : Module.finrank (ZMod 5) (Z.map ev) ≤ 1 := by
    have := Submodule.finrank_le (Z.map ev)
    rwa [Module.finrank_self] at this
  have hrn := rank_nullity Z ev
  have hZ2 : 1 ≤ Module.finrank (ZMod 5) ↥(Z ⊓ LinearMap.ker ev) := by omega
  have hne2 : Z ⊓ LinearMap.ker ev ≠ ⊥ := by
    intro h; rw [h, finrank_bot] at hZ2; omega
  obtain ⟨z1, hz1, hz1ne⟩ := Submodule.ne_bot_iff _ |>.1 hne2
  have := (hab z1 (Submodule.mem_inf.1 hz1).1 hz1ne).1
  exact this (Submodule.mem_inf.1 hz1).2


def rowr3 (r : Fin 3) : (Fin 3 × Fin 3 → (ZMod 5)) →ₗ[(ZMod 5)] (Fin 3 → (ZMod 5)) where
  toFun X := fun k => X (r, k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem p3_row_zero (r : Fin 3) (X : Fin 3 × Fin 3 → (ZMod 5)) (h : ∀ k, X (r, k) = 0) : p3 X = 0 := by
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  fin_cases r <;> simp only [p3] <;> simp_all

theorem p3_perm (r j : Fin 3) (X : Fin 3 × Fin 3 → (ZMod 5)) :
    p3 (X ∘ Equiv.prodCongr (Equiv.swap 0 r) (Equiv.swap 0 j)) = p3 X := by
  fin_cases r <;> fin_cases j <;>
    simp (config := { decide := true }) [p3, Equiv.swap_apply_def] <;> ring

theorem eq_zero_of_rows3 (X : Fin 3 × Fin 3 → (ZMod 5)) (h0 : ∀ k, X (0, k) = 0)
    (h1 : ∀ k, X (1, k) = 0) (h2 : ∀ k, X (2, k) = 0) : X = 0 := by
  funext q
  obtain ⟨i, k⟩ := q
  fin_cases i
  · exact h0 k
  · exact h1 k
  · exact h2 k

theorem F3 (L : Submodule (ZMod 5) (Fin 3 × Fin 3 → (ZMod 5))) (X0 : Fin 3 × Fin 3 → (ZMod 5))
    (hinv : ∀ X ∈ L ⊔ Submodule.span (ZMod 5) {X0}, ∀ y ∈ L, p3 (X + y) = p3 X) (hne : p3 X0 ≠ 0) :
    Module.finrank (ZMod 5) L ≤ 3 := by
  set C := L ⊔ Submodule.span (ZMod 5) {X0} with hC
  have hLC : L ≤ C := le_sup_left
  have hX0C : X0 ∈ C := Submodule.mem_sup_right (Submodule.mem_span_singleton_self X0)
  have hz : ∀ y ∈ L, p3 y = 0 := by
    intro y hy
    have := hinv 0 C.zero_mem y hy
    rw [zero_add] at this
    rw [this]; simp [p3]
  have hX0 : X0 ∉ L := fun h => hne (hz X0 h)
  have hCL : ∀ X ∈ C, p3 X = 0 → X ∈ L := by
    intro X hX h0
    obtain ⟨y, hy, m, hm, rfl⟩ := Submodule.mem_sup.1 hX
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hm
    have e := hinv (c • X0) (C.smul_mem c hX0C) y hy
    rw [add_comm] at h0
    rw [h0, p3_smul] at e
    have hc : c = 0 := by
      rcases mul_eq_zero.1 e.symm with h | h
      · exact pow_eq_zero_iff (n := 3) (by norm_num) |>.1 h
      · exact absurd h hne
    rw [hc, zero_smul, add_zero]; exact hy
  have hCdim : Module.finrank (ZMod 5) C = Module.finrank (ZMod 5) L + 1 := finrank_sup_span L X0 hX0
  by_contra hcon
  push Not at hcon
  have step1 : ∃ r, C.map (rowr3 r) = ⊤ := by
    by_contra hno
    push Not at hno
    have hK : ∀ r, Module.finrank (ZMod 5) L ≤ Module.finrank (ZMod 5) ↥(C ⊓ LinearMap.ker (rowr3 r)) + 1 := by
      intro r
      have h3 := Submodule.finrank_lt (hno r)
      rw [Module.finrank_fin_fun] at h3
      have := rank_nullity C (rowr3 r)
      omega
    have hKL : ∀ r, C ⊓ LinearMap.ker (rowr3 r) ≤ L := by
      intro r X hX
      obtain ⟨hXC, hXr⟩ := Submodule.mem_inf.1 hX
      apply hCL X hXC
      apply p3_row_zero r
      intro k
      exact congrFun (LinearMap.mem_ker.1 hXr) k
    set K0 := C ⊓ LinearMap.ker (rowr3 0)
    set K1 := C ⊓ LinearMap.ker (rowr3 1)
    set K2 := C ⊓ LinearMap.ker (rowr3 2)
    have hpair : ∀ A B : Submodule (ZMod 5) (Fin 3 × Fin 3 → (ZMod 5)), A ≤ L → B ≤ L →
        Module.finrank (ZMod 5) A + Module.finrank (ZMod 5) B ≤ Module.finrank (ZMod 5) ↥(A ⊓ B) + Module.finrank (ZMod 5) L := by
      intro A B hA hB
      have := Submodule.finrank_sup_add_finrank_inf_eq A B
      have := Submodule.finrank_mono (sup_le hA hB)
      omega
    have hall : ∀ X, X ∈ K0 → X ∈ K1 → X ∈ K2 → X = 0 := by
      intro X h0 h1 h2
      apply eq_zero_of_rows3
      · intro k; exact congrFun (LinearMap.mem_ker.1 (Submodule.mem_inf.1 h0).2) k
      · intro k; exact congrFun (LinearMap.mem_ker.1 (Submodule.mem_inf.1 h1).2) k
      · intro k; exact congrFun (LinearMap.mem_ker.1 (Submodule.mem_inf.1 h2).2) k
    have i1 : (K1 ⊓ K2) ⊓ (K0 ⊓ K2) = ⊥ := by
      rw [eq_bot_iff]; intro X hX
      simp only [Submodule.mem_inf] at hX
      rw [Submodule.mem_bot]; exact hall X hX.2.1 hX.1.1 hX.1.2
    have i2 : (K1 ⊓ K2 ⊔ K0 ⊓ K2) ⊓ (K0 ⊓ K1) = ⊥ := by
      rw [eq_bot_iff]; intro X hX
      obtain ⟨hX1, hX2⟩ := Submodule.mem_inf.1 hX
      have hK2 : X ∈ K2 := (sup_le inf_le_right inf_le_right : K1 ⊓ K2 ⊔ K0 ⊓ K2 ≤ K2) hX1
      rw [Submodule.mem_bot]
      exact hall X (Submodule.mem_inf.1 hX2).1 (Submodule.mem_inf.1 hX2).2 hK2
    have d1 := Submodule.finrank_sup_add_finrank_inf_eq (K1 ⊓ K2) (K0 ⊓ K2)
    rw [i1, finrank_bot] at d1
    have d2 := Submodule.finrank_sup_add_finrank_inf_eq (K1 ⊓ K2 ⊔ K0 ⊓ K2) (K0 ⊓ K1)
    rw [i2, finrank_bot] at d2
    have hle : K1 ⊓ K2 ⊔ K0 ⊓ K2 ⊔ K0 ⊓ K1 ≤ L :=
      sup_le (sup_le (inf_le_left.trans (hKL 1)) (inf_le_left.trans (hKL 0)))
        (inf_le_left.trans (hKL 0))
    have d3 := Submodule.finrank_mono hle
    have p12 := hpair K1 K2 (hKL 1) (hKL 2)
    have p02 := hpair K0 K2 (hKL 0) (hKL 2)
    have p01 := hpair K0 K1 (hKL 0) (hKL 1)
    have k0 : Module.finrank (ZMod 5) L ≤ Module.finrank (ZMod 5) K0 + 1 := hK 0
    have k1 : Module.finrank (ZMod 5) L ≤ Module.finrank (ZMod 5) K1 + 1 := hK 1
    have k2 : Module.finrank (ZMod 5) L ≤ Module.finrank (ZMod 5) K2 + 1 := hK 2
    omega
  obtain ⟨r, hr⟩ := step1
  have hsurj : ∀ v : Fin 3 → (ZMod 5), ∃ X ∈ C, rowr3 r X = v := by
    intro v
    have : v ∈ C.map (rowr3 r) := by rw [hr]; trivial
    obtain ⟨X, hX, hXv⟩ := Submodule.mem_map.1 this
    exact ⟨X, hX, hXv⟩
  have step2 : ∃ j, ∃ X ∈ C, rowr3 r X = Pi.single j 1 ∧ X ∉ L := by
    by_contra hno
    push Not at hno
    choose Xf hXfC hXfr using fun j => hsurj (Pi.single j 1)
    have hXfL : ∀ j, Xf j ∈ L := fun j => hno j (Xf j) (hXfC j) (hXfr j)
    set Y := X0 - ∑ j, X0 (r, j) • Xf j with hY
    have hYC : Y ∈ C := C.sub_mem hX0C (C.sum_mem fun j _ => C.smul_mem _ (hXfC j))
    have hYr : rowr3 r Y = 0 := by
      rw [hY, map_sub, map_sum]
      simp only [map_smul, hXfr]
      funext k
      simp [rowr3, Finset.sum_apply, Pi.single_apply]
    have hYL : Y ∈ L := hCL Y hYC (p3_row_zero r Y (fun k => congrFun hYr k))
    have hsumL : ∑ j, X0 (r, j) • Xf j ∈ L := L.sum_mem fun j _ => L.smul_mem _ (hXfL j)
    apply hX0
    have := L.add_mem hYL hsumL
    rwa [hY, sub_add_cancel] at this
  obtain ⟨j, Xs, hXsC, hXsr, hXsL⟩ := step2
  have hXsne : p3 Xs ≠ 0 := fun h => hXsL (hCL Xs hXsC h)
  set e := Equiv.prodCongr (Equiv.swap (0 : Fin 3) r) (Equiv.swap (0 : Fin 3) j) with he
  set T : (Fin 3 × Fin 3 → (ZMod 5)) ≃ₗ[(ZMod 5)] (Fin 3 × Fin 3 → (ZMod 5)) := LinearEquiv.funCongrLeft (ZMod 5) (ZMod 5) e with hT
  have hTapp : ∀ X q, T X q = X (e q) := fun X q => rfl
  have hTp3 : ∀ X, p3 (T X) = p3 X := fun X => p3_perm r j X
  have hmapC : C.map T.toLinearMap = L.map T.toLinearMap ⊔ Submodule.span (ZMod 5) {T X0} := by
    rw [hC, Submodule.map_sup, Submodule.map_span, Set.image_singleton]
    rfl
  have hsw : ∀ k : Fin 3, k ≠ 0 → Equiv.swap (0 : Fin 3) j k ≠ j := by
    intro k hk h
    apply hk
    apply (Equiv.swap (0 : Fin 3) j).injective
    rw [h, Equiv.swap_apply_left]
  obtain ⟨V1, hV1C, hV1r⟩ := hsurj (Pi.single (Equiv.swap (0 : Fin 3) j 1) 1)
  obtain ⟨V2, hV2C, hV2r⟩ := hsurj (Pi.single (Equiv.swap (0 : Fin 3) j 2) 1)
  have hrowv : ∀ (X : Fin 3 × Fin 3 → (ZMod 5)) (v : Fin 3 → (ZMod 5)), rowr3 r X = v → ∀ k, X (r, k) = v k :=
    fun X v h k => congrFun h k
  have hTr : ∀ X k, T X (0, k) = X (r, Equiv.swap (0 : Fin 3) j k) := by
    intro X k
    rw [hTapp]
    simp [he, Equiv.swap_apply_left]
  have hmemT : ∀ X ∈ C, T X ∈ L.map T.toLinearMap ⊔ Submodule.span (ZMod 5) {T X0} := by
    intro X hX
    rw [← hmapC]
    exact Submodule.mem_map_of_mem hX
  have key := F3_core (L.map T.toLinearMap) (T X0) ?_ (T Xs) (hmemT Xs hXsC) ?_ ?_ ?_ ?_
    (T V1) (hmemT V1 hV1C) ?_ ?_ (T V2) (hmemT V2 hV2C) ?_ ?_
  · rw [LinearEquiv.finrank_map_eq] at key
    omega
  · intro X hX y hy
    rw [← hmapC] at hX
    obtain ⟨X1, hX1, rfl⟩ := Submodule.mem_map.1 hX
    obtain ⟨y1, hy1, rfl⟩ := Submodule.mem_map.1 hy
    have h1 : T.toLinearMap X1 + T.toLinearMap y1 = T (X1 + y1) := by simp
    rw [h1]
    change p3 (T (X1 + y1)) = p3 (T X1)
    rw [hTp3, hTp3]
    exact hinv X1 hX1 y1 hy1
  · rw [hTr, hrowv Xs _ hXsr, Equiv.swap_apply_left]; simp
  · rw [hTr, hrowv Xs _ hXsr, Pi.single_apply, if_neg (hsw 1 (by decide))]
  · rw [hTr, hrowv Xs _ hXsr, Pi.single_apply, if_neg (hsw 2 (by decide))]
  · rw [hTp3]; exact hXsne
  · rw [hTr, hrowv V1 _ hV1r]; simp
  · rw [hTr, hrowv V1 _ hV1r, Pi.single_apply, if_neg]
    intro h
    have := (Equiv.swap (0 : Fin 3) j).injective h
    exact absurd this (by decide)
  · rw [hTr, hrowv V2 _ hV2r, Pi.single_apply, if_neg]
    intro h
    have := (Equiv.swap (0 : Fin 3) j).injective h
    exact absurd this (by decide)
  · rw [hTr, hrowv V2 _ hV2r]; simp


def J3 : Fin 3 × Fin 3 → ZMod 5 := fun _ => 1

theorem sum_perm_succ {n : ℕ} (g : Equiv.Perm (Fin (n + 1)) → ZMod 5) :
    ∑ σ, g σ = ∑ a : Fin (n + 1), ∑ τ : Equiv.Perm (Fin n),
      g (Equiv.Perm.decomposeFin.symm (a, τ)) := by
  rw [← Equiv.Perm.decomposeFin.symm.sum_comp, Fintype.sum_prod_type]

theorem perm_eq_p3 (M : Fin 3 × Fin 3 → ZMod 5) :
    Matrix.permanent (Matrix.of fun (i j : Fin 3) => M (i, j)) = p3 M := by
  rw [Matrix.permanent]
  change ∑ σ : Equiv.Perm (Fin 3), ∏ i : Fin 3, M (σ i, i) = p3 M
  rw [sum_perm_succ]
  simp only [sum_perm_succ (n := 1), sum_perm_succ (n := 0)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.prod_univ_succ, Fin.prod_univ_zero,
    Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ,
    Fintype.sum_unique]
  simp (config := { decide := true }) [Equiv.swap_apply_def, p3]
  ring

theorem p3_J3 : p3 J3 = 6 := by
  simp [p3, J3]
  norm_num

theorem p3_J3_ne : p3 J3 ≠ 0 := by
  rw [p3_J3]
  exact six_ne0

theorem p3_diff3 (t : Fin 3 × Fin 3 → ZMod 5) :
    6 * p3 t = p3 (J3 + (3 : ZMod 5) • t) - 3 * p3 (J3 + (2 : ZMod 5) • t) +
      3 * p3 (J3 + t) - p3 (J3 + 0) := by
  simp [p3, J3]
  ring

theorem p3_zero_of_level (L : Submodule (ZMod 5) (Fin 3 × Fin 3 → ZMod 5))
    (hL : ∀ t ∈ L, p3 (J3 + t) = 6) (t : Fin 3 × Fin 3 → ZMod 5) (ht : t ∈ L) :
    p3 t = 0 := by
  have h0 : p3 (J3 + 0) = 6 := hL 0 L.zero_mem
  have h1 : p3 (J3 + t) = 6 := hL t ht
  have h2 : p3 (J3 + (2 : ZMod 5) • t) = 6 := hL ((2 : ZMod 5) • t) (L.smul_mem 2 ht)
  have h3 : p3 (J3 + (3 : ZMod 5) • t) = 6 := hL ((3 : ZMod 5) • t) (L.smul_mem 3 ht)
  have hd := p3_diff3 t
  rw [h0, h1, h2, h3, six_eq1, one_mul] at hd
  rw [hd]
  exact six_sub_six

theorem p3_inv_of_level (L : Submodule (ZMod 5) (Fin 3 × Fin 3 → ZMod 5))
    (hL : ∀ t ∈ L, p3 (J3 + t) = 6) :
    ∀ X ∈ L ⊔ Submodule.span (ZMod 5) {J3}, ∀ y ∈ L, p3 (X + y) = p3 X := by
  intro X hX y hy
  obtain ⟨t, ht, m, hm, rfl⟩ := Submodule.mem_sup.1 hX
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hm
  by_cases hc : c = 0
  · subst hc
    simp only [zero_smul, add_zero]
    rw [p3_zero_of_level L hL (t + y) (L.add_mem ht hy), p3_zero_of_level L hL t ht]
  · have h1 : t + c • J3 = c • (J3 + c⁻¹ • t) := by
      rw [smul_add, smul_smul, mul_inv_cancel₀ hc, one_smul, add_comm]
    have h2 : t + c • J3 + y = c • (J3 + c⁻¹ • (t + y)) := by
      rw [smul_add, smul_smul, mul_inv_cancel₀ hc, one_smul]
      abel
    rw [h2, h1, p3_smul, p3_smul, hL _ (L.smul_mem c⁻¹ (L.add_mem ht hy)),
      hL _ (L.smul_mem c⁻¹ ht)]

theorem main_proof (L : Submodule (ZMod 5) (Fin 3 × Fin 3 → ZMod 5))
    (hdim : Module.finrank (ZMod 5) L = 4)
    (hperm : ∀ t ∈ L, Matrix.permanent (Matrix.of fun (i j : Fin 3) => (1 : ZMod 5) + t (i, j)) = 6) :
    False := by
  have hL : ∀ t ∈ L, p3 (J3 + t) = 6 := by
    intro t ht
    have h := hperm t ht
    change Matrix.permanent (Matrix.of fun (i j : Fin 3) => (J3 + t) (i, j)) = 6 at h
    rw [perm_eq_p3] at h
    exact h
  have hle := F3 L J3 (p3_inv_of_level L hL) p3_J3_ne
  omega

end WithFact

end PEqualNP.Outside.L_gct_226

theorem PEqualNP.Outside.L_gct_226 : ¬ (∃ L : Submodule (ZMod 5) (Fin 3 × Fin 3 → ZMod 5), Module.finrank (ZMod 5) L = 4 ∧ ∀ t ∈ L, Matrix.permanent (Matrix.of fun (i j : Fin 3) => (1 : ZMod 5) + t (i, j)) = 6) := by
  rintro ⟨L, hdim, hperm⟩
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact PEqualNP.Outside.L_gct_226.main_proof L hdim hperm
