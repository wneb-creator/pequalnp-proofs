import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_650_aux.FiveOwnerBudget

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

-- Extracted from the generic local argument in accepted R-meta-5060-52.
-- This theorem concerns AndCountCircuit; no conversion or gate-count preservation
-- for a different circuit representation is asserted here.

theorem sideEq {n k} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k) (v : Fin k → Bool) :
    sideTrue U B F i v = decide ((∃ u ∈ B, u ∈ U) ∨ ∃ j ∈ F, j < i ∧ v j = true) := rfl

theorem outEq {n} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    C.eval U = decide ((∃ u ∈ C.outVars, u ∈ U) ∨ ∃ j ∈ C.outGates, C.gateVal U j = true) := rfl

theorem fuelEq {n} (C : AndCountCircuit n) (U : Finset (Fin n)) (a : Nat) (i : Fin C.size) :
    C.gateValFuel U (a+1) i =
      (sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateValFuel U a) &&
       sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateValFuel U a)) := rfl

def wing {n} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) (b : Bool) :=
  sideTrue U (if b then C.rightVars i else C.leftVars i)
    (if b then C.rightGates i else C.leftGates i) i (C.gateVal U)

theorem stable {n} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size)
    (a b : Nat) (ha : i.val < a) (hb : i.val < b) :
    C.gateValFuel U a i = C.gateValFuel U b i := by
  induction a generalizing i b with
  | zero => omega
  | succ a ih =>
    cases b with
    | zero => omega
    | succ b =>
      have eq (B : Finset (Fin n)) (F : Finset (Fin C.size)) :
          sideTrue U B F i (C.gateValFuel U a) = sideTrue U B F i (C.gateValFuel U b) := by
        rw [sideEq,sideEq]
        congr 1
        apply propext
        constructor <;> rintro (raw | ⟨j,hj,lt,val⟩)
        · exact Or.inl raw
        · have h := ih j b (by change j.val < i.val at lt; omega) (by change j.val < i.val at lt; omega)
          exact Or.inr ⟨j,hj,lt,h ▸ val⟩
        · exact Or.inl raw
        · have h := ih j b (by change j.val < i.val at lt; omega) (by change j.val < i.val at lt; omega)
          exact Or.inr ⟨j,hj,lt,h.symm ▸ val⟩
      rw [fuelEq,fuelEq,eq,eq]

theorem value {n} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal U i = (wing C U i false && wing C U i true) :=
  stable C U i C.size (C.size+1) i.isLt (by omega)

theorem unionChoice {n} (C : AndCountCircuit n) (U V : Finset (Fin n)) (q : Fin C.size → Bool)
    (goodU : ∀ i, wing C U i (q i) = C.gateVal U i)
    (goodV : ∀ i, wing C V i (q i) = C.gateVal V i) :
    C.eval (U ∪ V) = true → C.eval U = true ∨ C.eval V = true := by
  have gates (d : Nat) : ∀ i : Fin C.size, C.gateValFuel (U ∪ V) d i = true →
      C.gateVal U i = true ∨ C.gateVal V i = true := by
    induction d with
    | zero => intro i h; cases h
    | succ d ih =>
      intro i h
      have both := Bool.and_eq_true_iff.mp h
      have pick : sideTrue (U ∪ V) (if q i then C.rightVars i else C.leftVars i)
          (if q i then C.rightGates i else C.leftGates i) i (C.gateValFuel (U ∪ V) d) = true := by
        cases q i
        · exact both.1
        · exact both.2
      rw [← goodU i, ← goodV i]
      simp only [wing,sideEq,decide_eq_true_eq] at pick ⊢
      rcases pick with ⟨v,hv,hmem⟩ | ⟨j,hj,hlt,on⟩
      · rcases Finset.mem_union.mp hmem with h | h
        · exact Or.inl (Or.inl ⟨v,hv,h⟩)
        · exact Or.inr (Or.inl ⟨v,hv,h⟩)
      · rcases ih j on with h | h
        · exact Or.inl (Or.inr ⟨j,hj,hlt,h⟩)
        · exact Or.inr (Or.inr ⟨j,hj,hlt,h⟩)
  simp only [outEq,decide_eq_true_eq]
  rintro (⟨v,hv,vhit⟩|⟨i,hi,hit⟩)
  · rcases Finset.mem_union.mp vhit with h | h
    · exact Or.inl (Or.inl ⟨v,hv,h⟩)
    · exact Or.inr (Or.inl ⟨v,hv,h⟩)
  · rcases gates C.size i hit with h | h
    · exact Or.inl (Or.inr ⟨i,hi,h⟩)
    · exact Or.inr (Or.inr ⟨i,hi,h⟩)

def free {n} (C : AndCountCircuit n) (U : Finset (Fin n)) : Finset (Fin C.size) :=
  Finset.univ.filter fun i => wing C U i false = wing C U i true

def encode {n} (C : AndCountCircuit n) (U : Finset (Fin n)) (s : Finset (Fin C.size)) :
    Fin C.size → Bool := fun i => if i ∈ free C U then decide (i ∈ s) else wing C U i false

theorem good {n} (C : AndCountCircuit n) (U : Finset (Fin n)) (s : Finset (Fin C.size))
    (i : Fin C.size) : wing C U i (encode C U s i) = C.gateVal U i := by
  rw [value]
  simp only [encode,free,Finset.mem_filter,Finset.mem_univ,true_and]
  cases h : wing C U i false <;> cases h' : wing C U i true <;> by_cases hs : i ∈ s <;> simp [h,h',hs]

theorem packing {n} (C : AndCountCircuit n) (F : Finset (Finset (Fin n)))
    (neg : ∀ U ∈ F, C.eval U = false)
    (pos : ∀ U ∈ F, ∀ V ∈ F, U ≠ V → C.eval (U ∪ V) = true) :
    (∑ U ∈ F, 2 ^ (free C U).card) ≤ 2 ^ C.size := by
  classical
  let cubes := fun U => (free C U).powerset.image (encode C U)
  have card (U : Finset (Fin n)) : (cubes U).card = 2^(free C U).card := by
    unfold cubes
    rw [Finset.card_image_iff.mpr ?_, Finset.card_powerset]
    intro s hs t ht eq
    have ssub := Finset.mem_powerset.mp hs
    have tsub := Finset.mem_powerset.mp ht
    ext i
    by_cases hi : i ∈ free C U
    · have he := congrFun eq i
      simpa only [encode,ite_eq_left hi,decide_eq_decide] using he
    · exact iff_of_false (fun h => hi (ssub h)) (fun h => hi (tsub h))
  have dis : (F : Set (Finset (Fin n))).PairwiseDisjoint cubes := by
    intro U hu V hv ne
    apply Finset.disjoint_left.mpr
    intro q hq hq'
    obtain ⟨s,_,hs⟩ := Finset.mem_image.mp hq
    obtain ⟨t,_,ht⟩ := Finset.mem_image.mp hq'
    have both := unionChoice C U V q (hs ▸ good C U s) (ht ▸ good C V t) (pos U hu V hv ne)
    simp only [neg U hu,neg V hv, Bool.false_eq_true,or_self] at both
  calc
    _ = ∑ U ∈ F, (cubes U).card := by simp_rw [card]
    _ = (F.biUnion cubes).card := (Finset.card_biUnion dis).symm
    _ ≤ Fintype.card (Fin C.size → Bool) := Finset.card_le_univ _
    _ = _ := by simp


theorem weighted_slack_two {ι : Type} [DecidableEq ι]
    (S : Finset ι) (w : ι → ℕ) (h : (∑ s ∈ S, 2 ^ w s) ≤ S.card + 2) :
    (∀ s ∈ S, w s ≤ 1) ∧ (∑ s ∈ S, w s) ≤ 2 := by
  constructor
  · intro s hs
    have hc : (S.erase s).card + 1 = S.card := by
      simpa using Finset.sum_erase_add S (fun _ => (1 : ℕ)) hs
    have he := Finset.sum_erase_add S (fun t => 2 ^ w t) hs
    have hl : (S.erase s).card ≤ ∑ t ∈ S.erase s, 2 ^ w t := by
      calc
        _ = ∑ _t ∈ S.erase s, (1 : ℕ) := by simp
        _ ≤ _ := Finset.sum_le_sum fun t _ => Nat.one_le_two_pow
    have hp : 2 ^ w s ≤ 3 := by omega
    have hw : w s < 2 ^ w s := Nat.lt_two_pow_self
    have hwle : w s ≤ 2 := by omega
    by_contra hn
    have hw2 : w s = 2 := by omega
    norm_num [hw2] at hp
  · have hl : S.card + (∑ s ∈ S, w s) ≤ ∑ s ∈ S, 2 ^ w s := by
      calc
        _ = ∑ s ∈ S, (1 + w s) := by simp [Finset.sum_add_distrib]
        _ ≤ _ := Finset.sum_le_sum fun s _ => by
          have hw : w s < 2 ^ w s := Nat.lt_two_pow_self
          omega
    omega

theorem side_mono {n k} (U V B : Finset (Fin n)) (G : Finset (Fin k))
    (i : Fin k) (f g : Fin k → Bool) (hUV : U ⊆ V)
    (hfg : ∀ j, f j = true → g j = true) :
    sideTrue U B G i f = true → sideTrue V B G i g = true := by
  simp only [sideEq, decide_eq_true_eq]
  rintro (⟨u,hu,hin⟩ | ⟨j,hj,hlt,hon⟩)
  · exact Or.inl ⟨u,hu,hUV hin⟩
  · exact Or.inr ⟨j,hj,hlt,hfg j hon⟩

theorem fuel_mono {n} (C : AndCountCircuit n) (U V : Finset (Fin n)) (hUV : U ⊆ V) :
    ∀ d (i : Fin C.size), C.gateValFuel U d i = true → C.gateValFuel V d i = true := by
  intro d
  induction d with
  | zero => intro i h; cases h
  | succ d ih =>
    intro i h
    rw [fuelEq] at h ⊢
    obtain ⟨hl,hr⟩ := Bool.and_eq_true_iff.mp h
    apply Bool.and_eq_true_iff.mpr
    exact ⟨side_mono U V _ _ i _ _ hUV ih hl, side_mono U V _ _ i _ _ hUV ih hr⟩

theorem gate_mono {n} (C : AndCountCircuit n) (U V : Finset (Fin n)) (hUV : U ⊆ V)
    (i : Fin C.size) : C.gateVal U i = true → C.gateVal V i = true :=
  fuel_mono C U V hUV C.size i

theorem active_mem_free {n} (C : AndCountCircuit n) (U : Finset (Fin n))
    (i : Fin C.size) (h : C.gateVal U i = true) : i ∈ free C U := by
  rw [value] at h
  obtain ⟨hl,hr⟩ := Bool.and_eq_true_iff.mp h
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hl.trans hr.symm⟩

theorem thirty_family_budget {n} (C : AndCountCircuit n) (F : Finset (Finset (Fin n)))
    (hcard : F.card = 30) (hsize : C.size ≤ 5)
    (hneg : ∀ U ∈ F, C.eval U = false)
    (hpos : ∀ U ∈ F, ∀ V ∈ F, U ≠ V → C.eval (U ∪ V) = true) :
    (∑ U ∈ F, (free C U).card) ≤ 2 := by
  have h := packing C F hneg hpos
  have hp : 2 ^ C.size ≤ 32 := by
    calc
      _ ≤ 2 ^ 5 := Nat.pow_le_pow_right (by decide) hsize
      _ = 32 := rfl
  exact (weighted_slack_two F (fun U => (free C U).card) (by omega)).2

theorem active_supersets_bound {n} (C : AndCountCircuit n) (F : Finset (Finset (Fin n)))
    (hbudget : (∑ V ∈ F, (free C V).card) ≤ 2)
    (U : Finset (Fin n)) (i : Fin C.size) (hon : C.gateVal U i = true) :
    (F.filter fun V => U ⊆ V).card ≤ 2 := by
  let A := F.filter fun V => U ⊆ V
  have hactive : ∀ V ∈ A, i ∈ free C V := by
    intro V hV
    exact active_mem_free C V i (gate_mono C U V (Finset.mem_filter.mp hV).2 i hon)
  have hlow : A.card ≤ ∑ V ∈ A, (free C V).card := by
    calc
      _ = ∑ _V ∈ A, (1 : ℕ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun V hV =>
        Nat.succ_le_iff.mpr (Finset.card_pos.mpr ⟨i,hactive V hV⟩)
  have hsub : (∑ V ∈ A, (free C V).card) ≤ ∑ V ∈ F, (free C V).card :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => Nat.zero_le _)
  change A.card ≤ 2
  omega

theorem false_of_three_supersets {n} (C : AndCountCircuit n) (F : Finset (Finset (Fin n)))
    (hbudget : (∑ V ∈ F, (free C V).card) ≤ 2)
    (U : Finset (Fin n)) (hcount : 3 ≤ (F.filter fun V => U ⊆ V).card)
    (i : Fin C.size) : C.gateVal U i = false := by
  cases hv : C.gateVal U i
  · rfl
  · have h := active_supersets_bound C F hbudget U i hv
    omega

end PEqualNP.Outside.L_meta_650_aux.FiveOwnerBudget
