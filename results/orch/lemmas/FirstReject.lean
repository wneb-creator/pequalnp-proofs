import KernelFirstEngine
namespace PEqualNP.Outside.L_meta_10760_first

lemma reject_live {top : TopT} (htop : TopOk top)
    {E F : List (Bool × Nat × Nat)} {Q : List (Nat × Nat)} {fb : Nat × Nat}
    {Z K k t : Nat} {S : Finset Nat}
    (hk : k ≤ K) (hK : K ≤ 15) (hE1 : E.length ≤ 1)
    (hp : pOk Z Q = true) (hI : ∀ e ∈ Q, Imp E e.1 e.2)
    (hfb : fb = (1, 0) ∨ (Z = 0 ∧ fbOk E F fb = true))
    (hF : ∀ e ∈ F, Imp [e] 0 (k + E.length))
    (hmin : Imp E Z k)
    (hS : (S : Set Nat) ⊆ C (mz Z) (WZ E Z))
    (hl : Live Z0 (mz Z) (tz Z) k t S)
    (hpw : pwr E Z = 0 ∨ pwr E Z ∈ S)
    (M : List (Nat × Nat)) (hMf : mFull M = true)
    (hchk : ∀ p ∈ M, chkG top E Q fb Z K t p.1 p.2 = false) : False := by
  simp only [pOk, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hp
  obtain ⟨⟨hp0, hp1⟩, hp2⟩ := hp
  have nb : ∀ {x y : ℕ}, Nat.beq x y = false → x ≠ y := fun h e => by rw [e, Nat.beq_refl] at h; simp at h
  have hT : tz Z &&& mz Z = tz Z := by simp only [tz, nl, Nat.and_assoc, Nat.and_self]
  classical
  have hCS : C (mz Z) (S : Set ℕ) ⊆ C (mz Z) (WZ E Z) := by
    rintro x (hx | hx)
    · exact hS hx
    · exact Or.inr hx
  have hm : Min Z0 (mz Z) (tz Z) k t S :=
    ⟨hl, fun q hq hs => hmin q hq (hs.mono le_rfl hCS)⟩
  have hbd : ∀ x ∈ S, x &&& mz Z = x := by
    intro x hx
    rcases hS hx with ⟨w, _, rfl⟩ | h
    · rw [Nat.and_assoc, Nat.and_self]
    · simp at h; rcases h with rfl | rfl <;> simp
  obtain ⟨h0, h1⟩ := hm.proper hT (nb hp0) (nb hp1) hbd
  have hSW : (S : Set ℕ) ⊆ WZ E Z := by
    intro x hx
    rcases hS hx with h | h
    · exact h
    · simp at h; rcases h with rfl | rfl
      · exact absurd hx h0
      · exact absurd hx h1
  have hproj : ∀ e ∈ Q, mz e.1 &&& mz Z = mz e.1 ∧ tz e.1 ≠ 0 ∧ tz e.1 ≠ mz e.1 := by
    intro e he
    obtain ⟨⟨a, b⟩, c⟩ := hp2 e he
    exact ⟨Nat.eq_of_beq_eq_true a, nb b, nb c⟩
  have hno : ∀ e ∈ Q, ∀ q < e.2, ¬ Sol Z0 (mz e.1) (tz Z &&& mz e.1) q (C (mz e.1) (Im (mz e.1) S)) := by
    intro e he q hq hs
    have h3 := (hproj e he).1
    rw [tz_sub h3] at hs
    exact hI e he q hq (hs.mono le_rfl (C_mono (Im_WZ h3 hSW)))
  obtain ⟨a1, a2⟩ := avl_spec (mz Z) (rawL E)
  set v := ((avl (mz Z) (rawL E)).filter (fun s => decide (s ∈ S))).map (mkW (PZ Q)) with hv
  have hsub : v.Sublist ((avl (mz Z) (rawL E)).map (mkW (PZ Q))) := List.filter_sublist.map _
  have hvs : v.map W.s = (avl (mz Z) (rawL E)).filter (fun s => decide (s ∈ S)) := by
    rw [hv, List.map_map]; exact List.map_id _
  have hnd : (v.map W.s).Nodup := by
    rw [hvs]
    exact (a1.sublist List.filter_sublist).imp fun h => Nat.ne_of_gt h
  have hrep : Rep v S := by
    refine ⟨hnd, Finset.ext fun x => ?_⟩
    rw [List.mem_toFinset, hvs, List.mem_filter, a2]
    constructor
    · rintro ⟨_, hx⟩; simpa using hx
    · intro hx
      obtain ⟨w, hw, rfl⟩ := hSW hx
      exact ⟨⟨fun e => h0 (e ▸ hx), fun e => h1 (e ▸ hx), w, hw, rfl⟩, by simpa using hx⟩
  have hvm : ∀ w ∈ v, ∃ x ∈ rawL E, w = mkW (PZ Q) (x &&& mz Z) := by
    intro w hw
    rw [hv, List.mem_map] at hw
    obtain ⟨s, hs, rfl⟩ := hw
    obtain ⟨_, _, x, hx, rfl⟩ := (a2 s).1 (List.mem_of_mem_filter hs)
    exact ⟨x, hx, rfl⟩
  have hwok : ∀ w ∈ v, WOk (PZ Q) w := by
    intro w hw
    obtain ⟨x, _, rfl⟩ := hvm w hw; exact mkW_ok _ _
  have hcod : ∀ w ∈ v, w.r = RZ E Z w.s := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := hvm w hw
    have : x &&& mz Z ∈ WZ E Z := ⟨x, hx, rfl⟩
    change 3 = RZ E Z (x &&& mz Z)
    rw [RZ, if_pos this]
  have hgood : ∀ w ∈ v, Good (lz Z) w.s := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := hvm w hw; exact wire_good hx Z
  have hd0 : ∀ w ∈ v, w.d = 0 := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := hvm w hw; rfl
  have hPlen : (PZ Q).length = Q.length := by simp [PZ]
  have hPget : ∀ j < (PZ Q).length, (PZ Q).getD j 0 = mz (Q.getD j (0, K)).1 ∧ Q.getD j (0, K) ∈ Q := by
    intro j hj
    rw [hPlen] at hj
    simp [PZ, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]
  have X : Ctx (PZ Q) (lz Z) (mz Z) (pL (Q.map fun _ => 16)) (npOf (PZ Q)) (tz Z) := by
    refine ⟨fun i hi => lz_lg Z i hi, fun j hj => ?_, ?_, ⟨fun j => (PZ Q).getD j 0, fun j _ => PZ_lt Q j, npOf_eq _, fun j _ _ => Nat.and_self _⟩⟩
    · obtain ⟨e1, e2⟩ := hPget j hj
      have h3 := hproj _ e2
      rw [e1, tz_sub h3.1]; exact h3
    · rw [pL_pk, List.length_map, hPlen]
      refine pk_congr fun j hj => ?_
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]; rfl
  have hA : ∀ j < (PZ Q).length, Acc ((PZ Q).getD j 0) (tz Z) K (K - (Q.getD j (0, K)).2) (fun _ => 0) S := by
    intro j hj
    obtain ⟨e1, e2⟩ := hPget j hj
    rw [e1]
    exact Acc.start (L := (Q.getD j (0, K)).2) (hno _ e2) subset_rfl (by omega)
  have hle := cnt_le X (D := fun _ _ => 0) hrep hwok hA hm (by omega)
  have hz : pL (Q.map fun e => 16 + (K - e.2)) - sumc v = pk (PZ Q).length (fun j => 16 + (K - (Q.getD j (0, K)).2) - cnt v j) := by
    rw [sumc_eq hwok, pk16, pk_sub]
    intro j hj; have := hle j hj; omega
  have hst : StOk (PZ Q) (tz Z) (lz Z) K (pL (Q.map fun e => 16 + (K - e.2)) - sumc v) v S := by
    rw [hz]
    exact StOk.start hrep hwok hgood (by omega) (fun j _ => by omega) hd0 hA
  have hcov : ∀ i, (lz Z).testBit i = true → (0 : ℕ).testBit i = true ∨ (cov (pos t) (lz Z) v).testBit i = true := by
    intro i hli
    right
    rw [cov_bit]
    obtain ⟨⟨m1, m2, t1, t2⟩, _⟩ := lz_lg Z i hli
    obtain ⟨w, hw, hs⟩ := hl.cov m1 m2 t1 t2
    obtain ⟨w', hw', rfl⟩ := hrep.mem.1 hw
    exact ⟨w', hw', by rw [sp_bit, hli, show pos t = pos' t by cases t <;> simp [pos, pos'], hs]; rfl⟩
  have hsz := hm.size.1
  have hcard := hrep.card
  have hble : Nat.ble (lnW v) (Nat.sub (Nat.succ K) t) = true := Nat.ble_eq_true_of_le (by
    rw [lnW_eq]; change v.length ≤ K + 1 - t; omega)
  have hhas : hasP (pwr E Z) v = true := hasP_ok (hpw.imp id fun h => hrep.mem.1 h)
  have all : ∀ p ∈ M, top (lz Z) (mz Z) (pL (Q.map fun _ => 16)) (npOf (PZ Q)) fb.1 fb.2 K p.1 p.2 K t (pL (Q.map fun e => 16 + (K - e.2)) - sumc v) v = false := by
    intro p hpM
    have h2 := hchk p hpM
    simp only [chkG, st_eq, pre_eq] at h2
    have h3 := anySub_false (by simp) h2 v hsub hcov
    simp only [startG, bR, hhas, hble, Bool.cond_true] at h3
    exact child_sound X (f := fun z r => top (lz Z) (mz Z) _ (npOf (PZ Q)) fb.1 fb.2 K p.1 p.2 K t z r) (fun h => rfl) rfl hst hm (by omega) h3
  have hW : {x | RZ E Z x ≠ 0} ∪ (S : Set ℕ) = WZ E Z := by rw [RZ_set]; exact Set.union_eq_self_of_subset_right hSW
  refine htop X (RZ_RR E Z) (RZ_R2 E Z) (Fs := {s | ∃ f ∈ F, s = tw f &&& mz Z ∧ Z = 0}) hMf all hst hcod (by omega) hl ?_ ?_ ?_
  · intro q hq hs
    rw [hW] at hs
    exact hmin q hq hs
  · intro d x y hxy hx hy hbit
    rcases hfb with rfl | ⟨rfl, hfb⟩
    · rw [fbit_triv] at hbit; simp at hbit
    · obtain ⟨f, hf, e⟩ := fbOk_spec hfb (RZ_mem hx) (RZ_mem hy) hxy hbit
      exact ⟨f, hf, e, rfl⟩
  · rintro s ⟨f, hf, rfl, rfl⟩ q hq hs
    rw [hW] at hs
    exact forb_ok hE1 (hF f hf) q (by omega) hs
end PEqualNP.Outside.L_meta_10760_first
