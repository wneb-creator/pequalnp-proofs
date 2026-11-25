import PEqualNP.Outside.L_meta_2592
namespace PEqualNP.Outside.L_meta_2592.Signed

lemma live_two_constants_bound {k : Nat} {S : Finset Extended.Sig} {a b : Extended.Sig}
    (run : Extended.Live true Extended.target k S)
    (rows : Row → Extended.Row)
    (same : restrictRows rows (Extended.observe Extended.target) = observe graph)
    (distinct : a ≠ b) (member : a ∈ S) (memberB : b ∈ S)
    (fixed : Constant (restrictRows rows (Extended.observe a)))
    (fixedB : Constant (restrictRows rows (Extended.observe b)))
    (supplied : ∀ v ∈ S,
      Available true (inputs.map observe) (restrictRows rows (Extended.observe v))) :
    17 ≤ k := by
  classical
  let front := a :: b :: ((S.erase a).erase b).toList
  have nd : front.Nodup := by
    apply List.nodup_cons.mpr
    constructor
    · simp [distinct]
    · apply List.nodup_cons.mpr
      exact ⟨by simp, Finset.nodup_toList _⟩
  have eqS : front.toFinset = S := by
    ext v
    by_cases va : v = a <;> by_cases vb : v = b <;> simp [front, va, vb, member, memberB]
  have hrun := Extended.list_run run front nd eqS
  have sup : supply true (inputs.map observe)
      ((front.map Extended.observe).map (restrictRows rows)) := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hw
    exact supplied z (eqS ▸ List.mem_toFinset.mpr hz)
  have bound := projected_bound rows hrun (same ▸ observe_proper graph_proper)
    Reach.start sup (L := 15) (by
      intro q bs reach hit
      apply nineFloor q bs reach
      rwa [same] at hit)
  have charge : 2 ≤ mass ((front.map Extended.observe).map (restrictRows rows)) := by
    simp [front, mass_cons, cost, fixed, fixedB]
    omega
  omega

end PEqualNP.Outside.L_meta_2592.Signed
namespace PEqualNP.Outside.L_meta_2592.Signed.Extended

def orAndBase (i j c : Fin 10) : Nat :=
  ([
  0,0,0,0,0,0,0,0,0,0,0,0,128,128,128,128,128,128,128,128,
  0,48,0,48,48,96,48,48,48,48,0,272,272,0,272,384,272,272,272,272,
  0,64,64,64,0,64,64,64,64,64,0,16,16,16,16,0,16,16,16,16,
  0,20,20,20,20,68,0,20,20,20,0,65,65,65,129,65,65,0,65,65,
  0,72,72,72,136,72,72,72,0,72,0,18,18,18,18,130,18,18,18,0,
  0,0,512,512,512,512,512,512,512,512,0,0,0,0,0,0,0,0,0,0,
  32,0,0,32,32,32,32,32,32,32,260,0,260,0,260,260,768,260,260,260,
  68,0,68,68,0,68,96,68,68,68,20,0,20,20,20,0,48,20,20,20,
  4,0,4,4,4,4,0,4,4,4,5,0,5,5,5,5,513,0,5,5,
  40,0,520,40,40,40,40,40,0,40,34,0,514,34,34,34,34,34,34,0,
  0,513,0,513,513,513,513,768,513,513,128,0,0,128,128,128,128,128,128,128,
  0,0,0,0,0,0,0,0,0,0,256,256,0,0,256,256,256,256,256,256,
  65,65,0,65,0,65,65,192,65,65,144,272,0,144,144,0,144,144,144,144,
  5,5,0,5,5,5,0,260,5,5,1,1,0,1,1,1,1,0,1,1,
  9,9,0,9,9,9,9,136,0,9,130,258,0,130,130,130,130,130,130,0,
  0,520,520,0,520,520,520,520,544,520,136,0,136,0,136,136,136,136,192,136,
  32,32,0,0,32,32,32,32,32,32,0,0,0,0,0,0,0,0,0,0,
  64,64,64,0,0,64,64,64,64,64,48,48,80,0,48,0,48,48,48,48,
  36,36,68,0,36,36,0,36,36,36,9,9,9,0,9,9,9,0,65,9,
  8,8,8,0,8,8,8,8,0,8,10,10,10,0,10,10,10,10,34,0,
  0,512,512,512,0,512,512,512,512,512,130,0,130,130,0,130,130,130,130,384,
  34,34,0,34,0,34,34,34,34,544,256,256,256,0,0,256,256,256,256,256,
  0,0,0,0,0,0,0,0,0,0,18,18,18,18,0,0,18,18,18,272,
  260,260,260,516,0,260,0,260,260,260,257,257,257,513,0,257,257,0,257,257,
  10,10,10,10,0,10,10,10,0,520,2,2,2,2,0,2,2,2,2,0,
  0,512,512,512,512,0,512,512,512,512,129,0,129,129,129,0,129,136,129,129,
  40,40,0,40,40,0,40,40,544,40,257,257,257,0,257,0,257,768,257,257,
  65,65,65,65,0,0,65,72,65,65,0,0,0,0,0,0,0,0,0,0,
  5,5,5,5,5,0,0,516,5,5,1,1,1,1,1,0,1,0,1,1,
  8,8,8,8,8,0,8,8,0,8,10,10,10,10,10,0,10,10,514,0,
  0,514,514,514,514,514,0,514,514,520,128,0,128,128,128,128,0,128,128,128,
  34,34,0,34,34,34,0,34,34,40,258,258,258,0,258,258,0,258,258,384,
  72,72,72,72,0,72,0,72,192,72,18,18,18,18,18,0,0,18,18,144,
  0,0,0,0,0,0,0,0,0,0,9,9,9,9,9,9,0,0,129,9,
  8,8,8,8,8,8,0,8,0,8,2,2,2,2,2,2,0,2,2,0,
  0,514,514,514,514,514,514,0,514,544,130,0,130,130,130,130,130,0,130,144,
  32,32,0,32,32,32,32,0,32,32,258,258,258,0,258,258,258,0,258,272,
  80,80,80,80,0,96,80,0,80,80,16,16,16,16,16,0,16,0,16,16,
  20,20,20,20,20,36,0,0,20,20,0,0,0,0,0,0,0,0,0,0,
  10,10,10,10,10,10,10,0,0,40,2,2,2,2,2,2,2,0,2,0,
  0,516,516,516,516,516,768,516,0,516,144,0,144,144,144,384,144,144,0,144,
  36,36,0,36,36,36,48,36,0,36,256,256,256,0,256,256,256,256,0,256,
  68,68,68,68,0,68,80,68,0,68,16,16,16,16,16,0,16,16,0,16,
  4,4,4,4,4,4,0,4,0,4,5,5,5,5,5,5,257,0,0,5,
  0,0,0,0,0,0,0,0,0,0,18,18,18,18,18,258,18,18,0,0,
  0,513,513,513,513,513,513,516,513,0,129,0,129,129,129,129,129,192,129,0,
  36,36,0,36,36,36,96,36,36,0,257,257,257,0,257,257,257,260,257,0,
  64,64,64,64,0,64,64,64,64,0,20,20,20,20,20,0,80,20,20,0,
  4,4,4,4,4,4,0,4,4,0,1,1,1,1,1,1,1,0,1,0,
  9,9,9,9,9,9,9,72,0,0,0,0,0,0,0,0,0,0,0,0] : List Nat).getD (100*i.val + 10*j.val + c.val) 0

def orAndRows (i j c : Fin 10) : Row × Row :=
  (Fin.ofNat 1024 (orAndBase i j c),
    Fin.ofNat 1024 (orAndBase i j c +
      ([512,128,32,256,64,16,4,1,8,2] : List Nat).getD i.val 0))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma orAndChecked : ∀ (i j c : Fin 10), i ≠ j → i ≠ c → j ≠ c →
    let rs := orAndRows i j c
    bit rs.1 target ≠ bit rs.2 target ∧
    bit rs.1 (bin 1 (pins.getD i.val zero) (pins.getD j.val zero)) =
      bit rs.2 (bin 1 (pins.getD i.val zero) (pins.getD j.val zero)) ∧
    bit rs.1 (bin 0 (pins.getD i.val zero) (pins.getD c.val zero)) =
      bit rs.2 (bin 0 (pins.getD i.val zero) (pins.getD c.val zero)) ∧
    ∀ q : Fin 10, q ≠ i →
      bit rs.1 (pins.getD q.val zero) = bit rs.2 (pins.getD q.val zero) := by
  decide +kernel

lemma or_and_keep_input (i j c : Fin 10) (ij : i ≠ j) (ic : i ≠ c) (jc : j ≠ c)
    {k : Nat} {S : Finset Sig}
    (raw : ∀ v ∈ S, v ∈ pins ∨
      v = bin 1 (pins.getD i.val zero) (pins.getD j.val zero) ∨
      v = bin 0 (pins.getD i.val zero) (pins.getD c.val zero))
    (run : Live true target k S) : pins.getD i.val zero ∈ S := by
  by_contra missing
  obtain ⟨diff, leftSame, rightSame, othersSame⟩ := orAndChecked i j c ij ic jc
  obtain ⟨v, hv, changed⟩ := live_row_difference run diff
  rcases raw v hv with ordinary | rfl | rfl
  · obtain ⟨q, eq⟩ := (pin_mem v).mp ordinary
    have qi : q ≠ i := by
      rintro rfl
      exact missing (eq.symm ▸ hv)
    exact changed (eq ▸ othersSame q qi)
  · exact changed leftSame
  · exact changed rightSame

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pin_ne_and : ∀ (i c : Fin 10), i ≠ c →
    pins.getD i.val zero ≠ bin 0 (pins.getD i.val zero) (pins.getD c.val zero) := by
  decide +kernel

end PEqualNP.Outside.L_meta_2592.Signed.Extended
namespace PEqualNP.Outside.L_meta_2592.Signed.Extended

def pairOrAndBase (i j : Fin 10) : Nat :=
  ([
  0,4,1,8,2,1,2,2,4,1,4,0,1,4,2,1,2,2,16,1,
  1,1,0,1,1,8,1,2,1,4,8,4,1,0,2,1,2,2,4,1,
  2,2,1,2,0,1,8,16,2,1,1,1,8,1,1,0,1,2,1,4,
  2,2,1,2,8,1,0,8,2,1,2,2,2,2,16,2,8,0,2,4,
  4,16,1,4,2,1,2,2,0,1,1,1,4,1,1,4,1,4,1,0] : List Nat).getD (10*i.val + j.val) 0

def pairOrAndRows (i j : Fin 10) : Row × Row :=
  (Fin.ofNat 1024 (pairOrAndBase i j +
    ([512,128,32,256,64,16,4,1,8,2] : List Nat).getD i.val 0),
   Fin.ofNat 1024 (pairOrAndBase i j +
    ([512,128,32,256,64,16,4,1,8,2] : List Nat).getD j.val 0))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pairOrAndChecked : ∀ (i j : Fin 10), i ≠ j →
    let rs := pairOrAndRows i j
    bit rs.1 target ≠ bit rs.2 target ∧
    bit rs.1 (bin 1 (pins.getD i.val zero) (pins.getD j.val zero)) =
      bit rs.2 (bin 1 (pins.getD i.val zero) (pins.getD j.val zero)) ∧
    bit rs.1 (bin 0 (pins.getD i.val zero) (pins.getD j.val zero)) =
      bit rs.2 (bin 0 (pins.getD i.val zero) (pins.getD j.val zero)) ∧
    ∀ q : Fin 10, q ≠ i → q ≠ j →
      bit rs.1 (pins.getD q.val zero) = bit rs.2 (pins.getD q.val zero) := by
  decide +kernel

lemma pair_or_and_keep_input (i j : Fin 10) (ij : i ≠ j)
    {k : Nat} {S : Finset Sig}
    (raw : ∀ v ∈ S, v ∈ pins ∨
      v = bin 1 (pins.getD i.val zero) (pins.getD j.val zero) ∨
      v = bin 0 (pins.getD i.val zero) (pins.getD j.val zero))
    (run : Live true target k S) : pins.getD i.val zero ∈ S ∨ pins.getD j.val zero ∈ S := by
  by_contra missing
  push_neg at missing
  obtain ⟨diff, leftSame, rightSame, othersSame⟩ := pairOrAndChecked i j ij
  obtain ⟨v, hv, changed⟩ := live_row_difference run diff
  rcases raw v hv with ordinary | rfl | rfl
  · obtain ⟨q, eq⟩ := (pin_mem v).mp ordinary
    have qi : q ≠ i := by
      rintro rfl
      exact missing.1 (eq.symm ▸ hv)
    have qj : q ≠ j := by
      rintro rfl
      exact missing.2 (eq.symm ▸ hv)
    exact changed (eq ▸ othersSame q qi qj)
  · exact changed leftSame
  · exact changed rightSame

end PEqualNP.Outside.L_meta_2592.Signed.Extended
namespace PEqualNP.Outside.L_meta_2592.Signed

lemma or_and_retained_floor (i j c : Fin 10) (ic : i ≠ c)
    {k : Nat} {S : Finset Extended.Sig}
    (retained : Extended.pins.getD i.val Extended.zero ∈ S)
    (kept : Extended.bin 0 (Extended.pins.getD i.val Extended.zero)
      (Extended.pins.getD c.val Extended.zero) ∈ S)
    (raw : ∀ v ∈ S, v ∈ Extended.pins ∨
      v = Extended.bin 1 (Extended.pins.getD i.val Extended.zero)
        (Extended.pins.getD j.val Extended.zero) ∨
      v = Extended.bin 0 (Extended.pins.getD i.val Extended.zero)
        (Extended.pins.getD c.val Extended.zero))
    (run : Extended.Live true Extended.target k S) : 17 ≤ k := by
  let a := Extended.pins.getD i.val Extended.zero
  let b := Extended.pins.getD j.val Extended.zero
  let cPin := Extended.pins.getD c.val Extended.zero
  have aMem : a ∈ Extended.pins := (Extended.pin_mem _).mpr ⟨i, rfl⟩
  have bMem : b ∈ Extended.pins := (Extended.pin_mem _).mpr ⟨j, rfl⟩
  obtain ⟨rows, fixed, same, supplied⟩ := pin_projection_false a aMem
  have gateZero : restrictRows rows (Extended.observe (Extended.bin 0 a cPin)) =
      (fun _ => false) := by
    rw [Extended.obs_bin, restrict_comb, fixed]
    funext r
    simp [comb, combine]
  apply live_two_constants_bound run rows same (Extended.pin_ne_and i c ic)
    retained kept ⟨false, fixed⟩ ⟨false, gateZero⟩
  intro v hv
  rcases raw v hv with ordinary | rfl | rfl
  · exact supplied v ordinary
  · rw [Extended.obs_bin, restrict_comb, fixed]
    simpa [comb, combine, b] using supplied b bMem
  · exact Or.inr (Or.inl ⟨false, gateZero⟩)

lemma or_and_floor (i j c : Fin 10) (ij : i ≠ j) (ic : i ≠ c) (jc : j ≠ c)
    {k : Nat} {S : Finset Extended.Sig}
    (kept : Extended.bin 0 (Extended.pins.getD i.val Extended.zero)
      (Extended.pins.getD c.val Extended.zero) ∈ S)
    (raw : ∀ v ∈ S, v ∈ Extended.pins ∨
      v = Extended.bin 1 (Extended.pins.getD i.val Extended.zero)
        (Extended.pins.getD j.val Extended.zero) ∨
      v = Extended.bin 0 (Extended.pins.getD i.val Extended.zero)
        (Extended.pins.getD c.val Extended.zero))
    (run : Extended.Live true Extended.target k S) : 17 ≤ k :=
  or_and_retained_floor i j c ic (Extended.or_and_keep_input i j c ij ic jc raw run)
    kept raw run

lemma pair_or_and_floor (i j : Fin 10) (ij : i ≠ j)
    {k : Nat} {S : Finset Extended.Sig}
    (kept : Extended.bin 0 (Extended.pins.getD i.val Extended.zero)
      (Extended.pins.getD j.val Extended.zero) ∈ S)
    (raw : ∀ v ∈ S, v ∈ Extended.pins ∨
      v = Extended.bin 1 (Extended.pins.getD i.val Extended.zero)
        (Extended.pins.getD j.val Extended.zero) ∨
      v = Extended.bin 0 (Extended.pins.getD i.val Extended.zero)
        (Extended.pins.getD j.val Extended.zero))
    (run : Extended.Live true Extended.target k S) : 17 ≤ k := by
  obtain retained | retained := Extended.pair_or_and_keep_input i j ij raw run
  · exact or_and_retained_floor i j j ij retained kept raw run
  · have andSwap : Extended.bin 0 (Extended.pins.getD j.val Extended.zero)
        (Extended.pins.getD i.val Extended.zero) =
        Extended.bin 0 (Extended.pins.getD i.val Extended.zero)
          (Extended.pins.getD j.val Extended.zero) := by
      simp [Extended.bin, BitVec.and_comm]
    have orSwap : Extended.bin 1 (Extended.pins.getD j.val Extended.zero)
        (Extended.pins.getD i.val Extended.zero) =
        Extended.bin 1 (Extended.pins.getD i.val Extended.zero)
          (Extended.pins.getD j.val Extended.zero) := by
      simp [Extended.bin, BitVec.or_comm]
    apply or_and_retained_floor j i i (Ne.symm ij) retained (andSwap.symm ▸ kept) ?_ run
    intro v hv
    simpa only [orSwap, andSwap] using raw v hv

end PEqualNP.Outside.L_meta_2592.Signed
