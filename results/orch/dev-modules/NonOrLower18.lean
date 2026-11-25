import FullRunLower17

namespace PEqualNP.Outside.L_meta_2592.FullRun

open PEqualNP.Outside.L_meta_2592.SignedFloor

lemma ret_comb_constant_right {R : Type} (d : Nat) (bank : List (Wire R)) (a b : Wire R)
    (hc : Constant b) (ha : Available true bank a) (hb : Available true bank b) :
    Available true bank (comb d a b) := by
  unfold comb
  split_ifs
  · exact from_constant false (Or.inr hc) ha hb
  · exact from_constant true (Or.inr hc) ha hb
  · exact from_constant false (Or.inr (inv_constant hc)) ha (avail_inv rfl hb)
  · exact from_constant false (Or.inr hc) (avail_inv rfl ha) hb

lemma ret_tail_bound
    (H : ∀ (p : Nat) (bank : List (Wire (Fin 9 → Bool))),
      Reach true (retRaw 9) p bank → Available true bank structuralDeletedEdge → 15 ≤ p)
    (p q : Fin 10) (rest : List (Wire (Fin 10 → Bool)))
    (hp : ((fun x => x p) :: (fun x => x q) :: rest).Perm (retRaw 10))
    (s d : Nat)
    (ht : Run true structuralEdge s
      (comb d (fun x => x p) (fun x => x q) :: (fun x => x p) :: (fun x => x q) :: rest))
    (r : Fin 10) (hr : r = p ∨ r = q) :
    15 + cost (restrictRows (retProjection r) (comb d (fun x => x p) (fun x => x q))) +
      cost (restrictRows (retProjection r) (fun x => x p)) +
      cost (restrictRows (retProjection r) (fun x => x q)) ≤ s := by
  have hall : ∀ w ∈ retRaw 10,
      Available true (retRaw 9) (restrictRows (retProjection r) w) := by
    intro w hw
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hw
    exact ret_raw_available r i
  have hs : supply true (retRaw 9)
      ((comb d (fun x => x p) (fun x => x q) :: (fun x => x p) :: (fun x => x q) :: rest).map
        (restrictRows (retProjection r))) := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
    rcases List.mem_cons.mp hv with rfl | hv
    · rw [restrict_comb]
      rcases hr with hr | hr
      · rw [hr]
        exact ret_comb_constant d _ _ _ (ret_projection_constant p)
          (ret_raw_available p p) (ret_raw_available p q)
      · rw [hr]
        exact ret_comb_constant_right d _ _ _ (ret_projection_constant q)
          (ret_raw_available q p) (ret_raw_available q q)
    · exact hall v (hp.mem_iff.mp hv)
  have hl := projected_bound (rows := retProjection r) ht
    (by rw [ret_projection_goal]; exact ret_deleted_nonconstant)
    (p := 0) (roots := retRaw 9) (bank := retRaw 9) (L := 15)
    Reach.start hs (by
      intro j bank hj hv
      rw [ret_projection_goal] at hv
      exact H j bank hj hv)
  simp only [List.map_cons, mass_cons] at hl
  omega

lemma ret_and_head_constant (p q : Fin 10) (d : Nat) (hd : d = 0 ∨ d = 2) :
    Constant (restrictRows (retProjection p) (comb d (fun x => x p) (fun x => x q))) := by
  refine ⟨false, ?_⟩
  funext x
  rcases hd with rfl | rfl <;>
    simp [restrictRows, comb, combine, inv, ret_projection_zero]

lemma ret_rev_head_constant (p q : Fin 10) :
    Constant (restrictRows (retProjection q) (comb 3 (fun x => x p) (fun x => x q))) := by
  refine ⟨false, ?_⟩
  funext x
  simp [restrictRows, comb, combine, inv, ret_projection_zero]

lemma non_or_tail_lower17
    (H : ∀ (p : Nat) (bank : List (Wire (Fin 9 → Bool))),
      Reach true (retRaw 9) p bank → Available true bank structuralDeletedEdge → 15 ≤ p)
    (p q : Fin 10) (hpq : p ≠ q) (rest : List (Wire (Fin 10 → Bool)))
    (hp : ((fun x => x p) :: (fun x => x q) :: rest).Perm (retRaw 10))
    (s d : Nat) (hd : d = 0 ∨ d = 2 ∨ d = 3) (ka kb : Bool)
    (ht : Run true structuralEdge s
      (comb d (fun x => x p) (fun x => x q) ::
        kept ka (fun x => x p) (kept kb (fun x => x q) rest))) : 17 ≤ s := by
  obtain ⟨hka, hkb⟩ := first_keeps_both p q hpq rest (ret_rest_invariant p q rest hp) ht
  have ht' : Run true structuralEdge s
      (comb d (fun x => x p) (fun x => x q) :: (fun x => x p) :: (fun x => x q) :: rest) := by
    simpa [kept, hka, hkb] using ht
  rcases hd with h0 | h2 | rfl
  · have hl := ret_tail_bound H p q rest hp s d ht' p (Or.inl rfl)
    have hc := ret_and_head_constant p q d (Or.inl h0)
    simp only [cost, if_pos hc, if_pos (ret_projection_constant p)] at hl
    omega
  · have hl := ret_tail_bound H p q rest hp s d ht' p (Or.inl rfl)
    have hc := ret_and_head_constant p q d (Or.inr h2)
    simp only [cost, if_pos hc, if_pos (ret_projection_constant p)] at hl
    omega
  · have hl := ret_tail_bound H p q rest hp s 3 ht' q (Or.inr rfl)
    have hc := ret_rev_head_constant p q
    simp only [cost, if_pos hc, if_pos (ret_projection_constant q)] at hl
    omega

end PEqualNP.Outside.L_meta_2592.FullRun
