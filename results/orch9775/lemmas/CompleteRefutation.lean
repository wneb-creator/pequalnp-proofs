import WeightClassification
import GraphSymmetry
import PrivateProjection
import Projection63
import ResidualCodeExclusions
import P11
import P47
import P164
import P177
import P197
import P266
import P298
import P400
import P416
import P432
import P525
import P645
import P1034
import P1038
import P1216
import P1220
import P1290
import P2087
import P4293
import W127
import W1290
import W4757
import W8488
import W16256

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore

open DagTools

theorem cap_ten_impossible {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (short : D.length ≤ 24) (small : Bplus 14 D ≤ 10) : False := by
  obtain ⟨m, hm, eq, ht⟩ := small_classification h hc short
  have lo := surplus_ten h hc
  have bp : Bplus 14 D=10 := by omega
  have total := surplus_identity h
  rw [totalSurplus_split] at total
  have bz : Bzero 14 D≤1 := by omega
  have ten := ht small
  simp only [tenMasks,List.mem_cons,List.not_mem_nil,or_false] at ten
  rcases ten with rfl | rfl | rfl | rfl | rfl
  · exact Compact.excludeW127 h hc bz bp eq
  · exact Compact.excludeW1290 h hc bz bp eq
  · exact Compact.excludeW4757 h hc bz bp eq
  · exact Compact.excludeW8488 h hc bz bp eq
  · exact Compact.excludeW16256 h hc bz bp eq

theorem no_empty_surplus {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (short : D.length ≤ 24) : Bplus 14 D=11 ∧ Bzero 14 D=0 := by
  have total := surplus_identity h
  rw [totalSurplus_split] at total
  have high : 10 < Bplus 14 D := lt_of_not_ge (cap_ten_impossible h hc short)
  omega

theorem reject55 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (bz : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 55=ineligSet 14 D) : False := by
  have bound := projection55 h hc bz eq
  omega

theorem reject63 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (bz : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 63=ineligSet 14 D) : False := by
  have bound := projected_exclude63 h hc bz eq
  omega

theorem reject95 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (bz : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 95=ineligSet 14 D) : False := by
  have bound := projection95 h hc bz eq
  omega

theorem reject103 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (bz : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 103=ineligSet 14 D) : False := by
  have bound := projection103 h hc bz eq
  omega

theorem reject111 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (bz : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 111=ineligSet 14 D) : False := by
  exact residual_exclude111 h hc bz bp eq

theorem reject119 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (bz : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 119=ineligSet 14 D) : False := by
  have bound := projection119 h hc bz eq
  omega

theorem reject123 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (bz : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 123=ineligSet 14 D) : False := by
  have bound := projection123 h hc bz eq
  omega

theorem reject181 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (bz : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 181=ineligSet 14 D) : False := by
  have bound := projection181 h hc bz eq
  omega

theorem reject229 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (bz : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 229=ineligSet 14 D) : False := by
  have bound := projection229 h hc bz eq
  omega

theorem reject245 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (bz : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 245=ineligSet 14 D) : False := by
  have bound := projection245 h hc bz eq
  omega

theorem reject661 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (bz : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 661=ineligSet 14 D) : False := by
  have bound := projection661 h hc bz eq
  omega

theorem reject2213 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (bz : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 2213=ineligSet 14 D) : False := by
  exact residual_exclude2213 h hc bz bp eq

theorem reject2693 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (bz : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 2693=ineligSet 14 D) : False := by
  have bound := projection2693 h hc bz eq
  omega

theorem reject4245 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (bz : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 4245=ineligSet 14 D) : False := by
  have bound := projection4245 h hc bz eq
  omega

theorem reject4309 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (bz : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 4309=ineligSet 14 D) : False := by
  have bound := projection4309 h hc bz eq
  omega

theorem reject4757 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (bz : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 4757=ineligSet 14 D) : False := by
  exact residual_exclude4757 h hc bz bp eq

theorem reject5190 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (bz : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 5190=ineligSet 14 D) : False := by
  have bound := projection5190 h hc bz eq
  omega

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem smaller_closed {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (short : D.length ≤ 24) : False := by
  obtain ⟨m, mem, eq, _⟩ := small_classification h hc short
  have shift (i j : Nat) (a : Equiv.Perm V) (perm : auto a)
      (ei : mask i=ineligSet 14 D) (mv : (mask i).image a=mask j)
      (impossible : ∀ {E : Dag}, StrictLive 14 E → sem_Comp 14 adj E →
        Bzero 14 E=0 → Bplus 14 E=11 → mask j=ineligSet 14 E → False) : False := by
    obtain ⟨E, strict, comp, len, pat⟩ := move_case h hc short i j ei a perm mv
    obtain ⟨bp,bz⟩ := no_empty_surplus strict comp len
    exact impossible strict comp bz bp pat.symm
  have side {E : Dag} (eh : StrictLive 14 E) (ec : sem_Comp 14 adj E)
      (bz : Bzero 14 E=0) (bp : Bplus 14 E=11)
      (ee : mask 127=ineligSet 14 E) : False := by
    have bound := side127 eh ec bz ee
    omega
  simp only [elevenMasks,List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact shift 11 11 graphPerm0 auto0 eq (by decide +kernel) Compact.excludeP11
  · exact shift 44 11 graphPerm1 auto1 eq (by decide +kernel) Compact.excludeP11
  · exact shift 47 47 graphPerm0 auto0 eq (by decide +kernel) Compact.excludeP47
  · exact shift 55 55 graphPerm0 auto0 eq (by decide +kernel) reject55
  · exact shift 63 63 graphPerm0 auto0 eq (by decide +kernel) reject63
  · exact shift 95 95 graphPerm0 auto0 eq (by decide +kernel) reject95
  · exact shift 103 103 graphPerm0 auto0 eq (by decide +kernel) reject103
  · exact shift 111 111 graphPerm0 auto0 eq (by decide +kernel) reject111
  · exact shift 119 119 graphPerm0 auto0 eq (by decide +kernel) reject119
  · exact shift 123 123 graphPerm0 auto0 eq (by decide +kernel) reject123
  · exact shift 125 95 graphPerm1 auto1 eq (by decide +kernel) reject95
  · exact shift 126 123 graphPerm1 auto1 eq (by decide +kernel) reject123
  · exact shift 127 127 graphPerm0 auto0 eq (by decide +kernel) side
  · exact shift 164 164 graphPerm0 auto0 eq (by decide +kernel) Compact.excludeP164
  · exact shift 177 177 graphPerm0 auto0 eq (by decide +kernel) Compact.excludeP177
  · exact shift 181 181 graphPerm0 auto0 eq (by decide +kernel) reject181
  · exact shift 197 197 graphPerm0 auto0 eq (by decide +kernel) Compact.excludeP197
  · exact shift 229 229 graphPerm0 auto0 eq (by decide +kernel) reject229
  · exact shift 245 245 graphPerm0 auto0 eq (by decide +kernel) reject245
  · exact shift 266 266 graphPerm0 auto0 eq (by decide +kernel) Compact.excludeP266
  · exact shift 296 266 graphPerm1 auto1 eq (by decide +kernel) Compact.excludeP266
  · exact shift 298 298 graphPerm0 auto0 eq (by decide +kernel) Compact.excludeP298
  · exact shift 400 400 graphPerm0 auto0 eq (by decide +kernel) Compact.excludeP400
  · exact shift 416 416 graphPerm0 auto0 eq (by decide +kernel) Compact.excludeP416
  · exact shift 432 432 graphPerm0 auto0 eq (by decide +kernel) Compact.excludeP432
  · exact shift 521 400 graphPerm2 auto2 eq (by decide +kernel) Compact.excludeP400
  · exact shift 524 400 graphPerm3 auto3 eq (by decide +kernel) Compact.excludeP400
  · exact shift 525 525 graphPerm0 auto0 eq (by decide +kernel) Compact.excludeP525
  · exact shift 645 645 graphPerm0 auto0 eq (by decide +kernel) Compact.excludeP645
  · exact shift 661 661 graphPerm0 auto0 eq (by decide +kernel) reject661
  · exact shift 1034 1034 graphPerm0 auto0 eq (by decide +kernel) Compact.excludeP1034
  · exact shift 1036 416 graphPerm3 auto3 eq (by decide +kernel) Compact.excludeP416
  · exact shift 1038 1038 graphPerm0 auto0 eq (by decide +kernel) Compact.excludeP1038
  · exact shift 1156 164 graphPerm3 auto3 eq (by decide +kernel) Compact.excludeP164
  · exact shift 1216 1216 graphPerm0 auto0 eq (by decide +kernel) Compact.excludeP1216
  · exact shift 1220 1220 graphPerm0 auto0 eq (by decide +kernel) Compact.excludeP1220
  · exact shift 1282 1034 graphPerm2 auto2 eq (by decide +kernel) Compact.excludeP1034
  · exact shift 1288 266 graphPerm2 auto2 eq (by decide +kernel) Compact.excludeP266
  · exact shift 1290 1290 graphPerm0 auto0 eq (by decide +kernel) Compact.excludeP1290
  · exact shift 1408 11 graphPerm2 auto2 eq (by decide +kernel) Compact.excludeP11
  · exact shift 1548 432 graphPerm3 auto3 eq (by decide +kernel) Compact.excludeP432
  · exact shift 2051 1216 graphPerm2 auto2 eq (by decide +kernel) Compact.excludeP1216
  · exact shift 2084 1216 graphPerm3 auto3 eq (by decide +kernel) Compact.excludeP1216
  · exact shift 2087 2087 graphPerm0 auto0 eq (by decide +kernel) Compact.excludeP2087
  · exact shift 2212 1220 graphPerm3 auto3 eq (by decide +kernel) Compact.excludeP1220
  · exact shift 2213 2213 graphPerm0 auto0 eq (by decide +kernel) reject2213
  · exact shift 2693 2693 graphPerm0 auto0 eq (by decide +kernel) reject2693
  · exact shift 4099 164 graphPerm1 auto1 eq (by decide +kernel) Compact.excludeP164
  · exact shift 4118 177 graphPerm1 auto1 eq (by decide +kernel) Compact.excludeP177
  · exact shift 4119 181 graphPerm1 auto1 eq (by decide +kernel) reject181
  · exact shift 4165 197 graphPerm1 auto1 eq (by decide +kernel) Compact.excludeP197
  · exact shift 4167 229 graphPerm1 auto1 eq (by decide +kernel) reject229
  · exact shift 4183 245 graphPerm1 auto1 eq (by decide +kernel) reject245
  · exact shift 4241 645 graphPerm2 auto2 eq (by decide +kernel) Compact.excludeP645
  · exact shift 4244 645 graphPerm3 auto3 eq (by decide +kernel) Compact.excludeP645
  · exact shift 4245 4245 graphPerm0 auto0 eq (by decide +kernel) reject4245
  · exact shift 4293 4293 graphPerm0 auto0 eq (by decide +kernel) Compact.excludeP4293
  · exact shift 4305 2693 graphPerm2 auto2 eq (by decide +kernel) reject2693
  · exact shift 4308 2693 graphPerm3 auto3 eq (by decide +kernel) reject2693
  · exact shift 4309 4309 graphPerm0 auto0 eq (by decide +kernel) reject4309
  · exact shift 4354 416 graphPerm1 auto1 eq (by decide +kernel) Compact.excludeP416
  · exact shift 4368 400 graphPerm1 auto1 eq (by decide +kernel) Compact.excludeP400
  · exact shift 4370 432 graphPerm1 auto1 eq (by decide +kernel) Compact.excludeP432
  · exact shift 4496 525 graphPerm2 auto2 eq (by decide +kernel) Compact.excludeP525
  · exact shift 4613 645 graphPerm1 auto1 eq (by decide +kernel) Compact.excludeP645
  · exact shift 4629 661 graphPerm1 auto1 eq (by decide +kernel) reject661
  · exact shift 4741 4245 graphPerm2 auto2 eq (by decide +kernel) reject4245
  · exact shift 4753 661 graphPerm2 auto2 eq (by decide +kernel) reject661
  · exact shift 4756 661 graphPerm3 auto3 eq (by decide +kernel) reject661
  · exact shift 4757 4757 graphPerm0 auto0 eq (by decide +kernel) reject4757
  · exact shift 5190 5190 graphPerm0 auto0 eq (by decide +kernel) reject5190
  · exact shift 5316 2213 graphPerm3 auto3 eq (by decide +kernel) reject2213
  · exact shift 5378 1038 graphPerm2 auto2 eq (by decide +kernel) Compact.excludeP1038
  · exact shift 5636 177 graphPerm3 auto3 eq (by decide +kernel) Compact.excludeP177
  · exact shift 5764 181 graphPerm3 auto3 eq (by decide +kernel) reject181
  · exact shift 6147 1220 graphPerm2 auto2 eq (by decide +kernel) Compact.excludeP1220
  · exact shift 6151 2213 graphPerm1 auto1 eq (by decide +kernel) reject2213
  · exact shift 6273 197 graphPerm2 auto2 eq (by decide +kernel) Compact.excludeP197
  · exact shift 6276 197 graphPerm3 auto3 eq (by decide +kernel) Compact.excludeP197
  · exact shift 6277 4293 graphPerm2 auto2 eq (by decide +kernel) Compact.excludeP4293
  · exact shift 6661 2693 graphPerm1 auto1 eq (by decide +kernel) reject2693
  · exact shift 6789 4309 graphPerm2 auto2 eq (by decide +kernel) reject4309
  · exact shift 7174 5190 graphPerm2 auto2 eq (by decide +kernel) reject5190
  · exact shift 7300 229 graphPerm3 auto3 eq (by decide +kernel) reject229
  · exact shift 7812 245 graphPerm3 auto3 eq (by decide +kernel) reject245
  · exact shift 8064 95 graphPerm2 auto2 eq (by decide +kernel) reject95
  · exact shift 8201 416 graphPerm2 auto2 eq (by decide +kernel) Compact.excludeP416
  · exact shift 8232 1034 graphPerm1 auto1 eq (by decide +kernel) Compact.excludeP1034
  · exact shift 8233 1038 graphPerm1 auto1 eq (by decide +kernel) Compact.excludeP1038
  · exact shift 8417 5190 graphPerm1 auto1 eq (by decide +kernel) reject5190
  · exact shift 8456 266 graphPerm3 auto3 eq (by decide +kernel) Compact.excludeP266
  · exact shift 8480 1034 graphPerm3 auto3 eq (by decide +kernel) Compact.excludeP1034
  · exact shift 8488 1290 graphPerm1 auto1 eq (by decide +kernel) Compact.excludeP1290
  · exact shift 8608 1038 graphPerm3 auto3 eq (by decide +kernel) Compact.excludeP1038
  · exact shift 8713 432 graphPerm2 auto2 eq (by decide +kernel) Compact.excludeP432
  · exact shift 8833 177 graphPerm2 auto2 eq (by decide +kernel) Compact.excludeP177
  · exact shift 9480 298 graphPerm2 auto2 eq (by decide +kernel) Compact.excludeP298
  · exact shift 10401 5190 graphPerm3 auto3 eq (by decide +kernel) reject5190
  · exact shift 12160 123 graphPerm2 auto2 eq (by decide +kernel) reject123
  · exact shift 12289 164 graphPerm2 auto2 eq (by decide +kernel) Compact.excludeP164
  · exact shift 12352 1216 graphPerm1 auto1 eq (by decide +kernel) Compact.excludeP1216
  · exact shift 12353 1220 graphPerm1 auto1 eq (by decide +kernel) Compact.excludeP1220
  · exact shift 12481 2213 graphPerm2 auto2 eq (by decide +kernel) reject2213
  · exact shift 12544 11 graphPerm3 auto3 eq (by decide +kernel) Compact.excludeP11
  · exact shift 12929 181 graphPerm2 auto2 eq (by decide +kernel) reject181
  · exact shift 13504 2087 graphPerm2 auto2 eq (by decide +kernel) Compact.excludeP2087
  · exact shift 13696 47 graphPerm2 auto2 eq (by decide +kernel) Compact.excludeP47
  · exact shift 13952 55 graphPerm2 auto2 eq (by decide +kernel) reject55
  · exact shift 14208 63 graphPerm2 auto2 eq (by decide +kernel) reject63
  · exact shift 14465 229 graphPerm2 auto2 eq (by decide +kernel) reject229
  · exact shift 14977 245 graphPerm2 auto2 eq (by decide +kernel) reject245
  · exact shift 15232 95 graphPerm3 auto3 eq (by decide +kernel) reject95
  · exact shift 15488 103 graphPerm2 auto2 eq (by decide +kernel) reject103
  · exact shift 15744 111 graphPerm2 auto2 eq (by decide +kernel) reject111
  · exact shift 16000 119 graphPerm2 auto2 eq (by decide +kernel) reject119
  · exact shift 16128 123 graphPerm3 auto3 eq (by decide +kernel) reject123
  · exact shift 16256 127 graphPerm2 auto2 eq (by decide +kernel) side

end PEqualNP.Outside.L_meta_9775.UpstreamCore

theorem PEqualNP.Outside.L_meta_9775 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 24 ∧ (∀ x : Fin 14 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 14, (u.val, v.val) ∈ ([(0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true))) := by
  rintro ⟨C, hm, hs, hc⟩
  obtain ⟨D, hd, hsize, hcomp⟩ := PEqualNP.Outside.L_meta_9775.UpstreamCore.normalized C hm hc
  exact PEqualNP.Outside.L_meta_9775.UpstreamCore.smaller_closed hd hcomp (hsize.trans hs)
