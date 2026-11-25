import OperandRetentionFast
import Mathlib.Tactic.FinCases

namespace PEqualNP.Outside.L_meta_2592.FullRun

open PEqualNP.Outside.L_meta_2592.SignedFloor

def retRaw (n : Nat) : List (Wire (Fin n → Bool)) := List.ofFn fun i => fun x => x i

lemma ret_raw_injective (n : Nat) : Function.Injective (fun i : Fin n => fun x : Fin n → Bool => x i) := by
  intro i j h
  have hji : j = i := by
    simpa using (congrFun h (fun k => decide (k = i))).symm
  exact hji.symm

lemma ret_raw_nodup (n : Nat) : (retRaw n).Nodup :=
  List.nodup_ofFn.mpr (ret_raw_injective n)

noncomputable def retMoveEquiv (p : Fin 10) : Fin 10 ≃ Fin 10 :=
  Equiv.ofBijective (structuralMove p) (structural_move_bijective p)

noncomputable def retProjection (p : Fin 10) (x : Fin 9 → Bool) : Fin 10 → Bool :=
  fun i => structuralExtend x false ((retMoveEquiv p).symm i)

lemma ret_projection_zero (p : Fin 10) (x : Fin 9 → Bool) : retProjection p x p = false := by
  have hp : (retMoveEquiv p).symm p = 9 := by
    apply (retMoveEquiv p).injective
    rw [Equiv.apply_symm_apply]
    exact (structural_move_last p).symm
  unfold retProjection
  rw [hp]
  rfl

lemma ret_projection_goal (p : Fin 10) :
    restrictRows (retProjection p) structuralEdge = structuralDeletedEdge := by
  funext x
  change structuralEdge (retProjection p x) = structuralDeletedEdge x
  calc
    structuralEdge (retProjection p x) =
        structuralEdge (retProjection p x ∘ structuralMove p) :=
      (structural_move_edge p (retProjection p x)).symm
    _ = structuralEdge (structuralExtend x false) := by
      congr 1
      funext i
      change structuralExtend x false ((retMoveEquiv p).symm ((retMoveEquiv p) i)) = _
      rw [Equiv.symm_apply_apply]
    _ = structuralDeletedEdge x := structural_cofactor_false x

lemma ret_extend_cast (x : Fin 9 → Bool) (i : Fin 9) :
    structuralExtend x false i.castSucc = x i := by
  fin_cases i <;> rfl

lemma ret_raw_available (p i : Fin 10) :
    Available true (retRaw 9) (restrictRows (retProjection p) (fun x => x i)) := by
  classical
  let j := (retMoveEquiv p).symm i
  by_cases hj : j = 9
  · right
    left
    refine ⟨false, ?_⟩
    funext x
    change structuralExtend x false j = false
    rw [hj]
    rfl
  · have hjlt : j.val < 9 := by
      have hjten := j.isLt
      have hjne : j.val ≠ 9 := by
        intro he
        apply hj
        exact Fin.ext he
      omega
    let j9 : Fin 9 := ⟨j.val, hjlt⟩
    have heq : restrictRows (retProjection p) (fun x => x i) = fun x => x j9 := by
      funext x
      change structuralExtend x false j = x j9
      exact ret_extend_cast x j9
    left
    rw [heq]
    exact List.mem_ofFn.mpr ⟨j9, rfl⟩

lemma ret_projection_constant (p : Fin 10) :
    Constant (restrictRows (retProjection p) (fun x => x p)) := by
  refine ⟨false, ?_⟩
  funext x
  exact ret_projection_zero p x

lemma ret_comb_constant {R : Type} (d : Nat) (bank : List (Wire R)) (a b : Wire R)
    (hc : Constant a) (ha : Available true bank a) (hb : Available true bank b) :
    Available true bank (comb d a b) := by
  unfold comb
  split_ifs
  · exact from_constant false (Or.inl hc) ha hb
  · exact from_constant true (Or.inl hc) ha hb
  · exact from_constant false (Or.inl hc) ha (avail_inv rfl hb)
  · exact from_constant false (Or.inl (inv_constant hc)) (avail_inv rfl ha) hb

lemma ret_deleted_nonconstant : ¬ Constant structuralDeletedEdge := by
  rintro ⟨b, hb⟩
  have h0 := congrFun hb (fun _ => false)
  have h1 := congrFun hb (fun i => decide (i = 0 ∨ i = 1))
  have he := h0.trans h1.symm
  simpa [structuralDeletedEdge] using he

lemma ret_rest_invariant (p q : Fin 10) (rest : List (Wire (Fin 10 → Bool)))
    (hp : ((fun x => x p) :: (fun x => x q) :: rest).Perm (retRaw 10)) :
    ∀ w ∈ rest, ∀ (x : Fin 10 → Bool) (a b : Bool),
      w (structuralSetPair x p q a b) = w x := by
  have hn := hp.nodup_iff.mpr (ret_raw_nodup 10)
  have hn1 := (List.nodup_cons.mp hn).1
  have hn2 := (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1
  intro w hw x a b
  have hm : w ∈ retRaw 10 := hp.mem_iff.mp (by simp [hw])
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hm
  have hip : i ≠ p := by
    intro h
    subst i
    exact hn1 (List.mem_cons_of_mem _ hw)
  have hiq : i ≠ q := by
    intro h
    subst i
    exact hn2 hw
  simp [structuralSetPair, Function.update_of_ne hip, Function.update_of_ne hiq]

lemma fullRun_lower17_of_deleted_lower
    (H : ∀ (p : Nat) (bank : List (Wire (Fin 9 → Bool))),
      Reach true (retRaw 9) p bank → Available true bank structuralDeletedEdge → 15 ≤ p) :
    ∀ k : Nat, Run true structuralEdge k (retRaw 10) → 17 ≤ k := by
  intro k h
  cases k with
  | zero =>
    have hl := h.length_eq
    simp [retRaw] at hl
  | succ k =>
    obtain ⟨d, ka, kb, a, b, rest, hd, hp, ht⟩ := h
    have ha : a ∈ retRaw 10 := hp.mem_iff.mp (by simp)
    obtain ⟨p, rfl⟩ := List.mem_ofFn.mp ha
    have hb : b ∈ retRaw 10 := hp.mem_iff.mp (by simp)
    obtain ⟨q, rfl⟩ := List.mem_ofFn.mp hb
    have hn := hp.nodup_iff.mpr (ret_raw_nodup 10)
    have hpq : p ≠ q := by
      intro he
      subst q
      exact (List.nodup_cons.mp hn).1 (by simp)
    have hka := first_keeps_left p q hpq rest (ret_rest_invariant p q rest hp) ht
    have ht' : Run true structuralEdge k
        (comb d (fun x => x p) (fun x => x q) :: (fun x => x p) ::
          kept kb (fun x => x q) rest) := by
      simpa [kept, hka] using ht
    have hall : ∀ w ∈ retRaw 10,
        Available true (retRaw 9) (restrictRows (retProjection p) w) := by
      intro w hw
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hw
      exact ret_raw_available p i
    have hs : supply true (retRaw 9)
        ((comb d (fun x => x p) (fun x => x q) :: (fun x => x p) ::
          kept kb (fun x => x q) rest).map (restrictRows (retProjection p))) := by
      intro w hw
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
      rcases List.mem_cons.mp hv with rfl | hv
      · rw [restrict_comb]
        exact ret_comb_constant d _ _ _ (ret_projection_constant p)
          (ret_raw_available p p) (ret_raw_available p q)
      · apply hall
        apply hp.mem_iff.mp
        rcases List.mem_cons.mp hv with rfl | hv
        · simp
        · rcases kept_mem hv with rfl | hv
          · simp
          · simp [hv]
    have hl := projected_bound (rows := retProjection p) ht'
      (by rw [ret_projection_goal]; exact ret_deleted_nonconstant)
      (p := 0) (roots := retRaw 9) (bank := retRaw 9) (L := 15)
      Reach.start hs (by
        intro j bank hj hv
        rw [ret_projection_goal] at hv
        exact H j bank hj hv)
    have hc : cost (restrictRows (retProjection p) (fun x => x p)) = 1 := by
      simp [cost, ret_projection_constant p]
    simp only [List.map_cons, mass_cons, hc] at hl
    omega

end PEqualNP.Outside.L_meta_2592.FullRun
