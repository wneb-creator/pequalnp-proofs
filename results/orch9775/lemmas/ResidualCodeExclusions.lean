import CompactFramework

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore
open DagTools

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 8192 in
theorem residual_exclude111 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 111=ineligSet 14 D) : False := by
  classical
  obtain ⟨b,hb⟩ := sem_exists_pureBranch graph_ok h.1 hc
  have card := card_residual h.1 b hb
  have el := inelig_card_add 14 D
  rw [←eq] at el
  have count : (mask 111).card=6 := by decide +kernel
  have res : Fintype.card ↥(residualUnits 14 D b)=3 := by rw [Fintype.card_coe]; omega
  let f := (Fintype.equivFinOfCardEq res).symm
  have miss0 := two_exact h hc z (mask 6789) (by decide +kernel) 1 5 9 11 7 (eq ▸ (by decide +kernel : (1:V)∈mask 111)) (eq ▸ (by decide +kernel : (5:V)∈mask 111)) (by decide +kernel)
  have h0 := code_diff h hc b hb f 9 11 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (9:V)∉mask 111) hin : (9:V)∈eligSet 14 D) miss0 (share h hc (i:=6) (x:=9) (y:=11) (eq ▸ (by decide +kernel : (6:V)∈mask 111)) (by decide +kernel) (by decide +kernel))
  have miss1 := two_exact h hc z (mask 9992) (by decide +kernel) 5 6 9 13 10 (eq ▸ (by decide +kernel : (5:V)∈mask 111)) (eq ▸ (by decide +kernel : (6:V)∈mask 111)) (by decide +kernel)
  have h1 := code_diff h hc b hb f 9 13 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (9:V)∉mask 111) hin : (9:V)∈eligSet 14 D) miss1 (share h hc (i:=1) (x:=9) (y:=13) (eq ▸ (by decide +kernel : (1:V)∈mask 111)) (by decide +kernel) (by decide +kernel))
  have miss2 := exposed_exact h hc z (mask 9992) (mask 792) (by decide +kernel) (by decide +kernel) 0 10 9 (eq ▸ (by decide +kernel : (0:V)∈mask 111)) (by decide +kernel)
  have h2 := code_diff h hc b hb f 10 9 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (10:V)∉mask 111) hin : (10:V)∈eligSet 14 D) miss2 (share h hc (i:=5) (x:=10) (y:=9) (eq ▸ (by decide +kernel : (5:V)∈mask 111)) (by decide +kernel) (by decide +kernel))
  have miss3 := two_exact h hc z (mask 9992) (by decide +kernel) 0 5 10 13 8 (eq ▸ (by decide +kernel : (0:V)∈mask 111)) (eq ▸ (by decide +kernel : (5:V)∈mask 111)) (by decide +kernel)
  have h3 := code_excludes h hc b hb f 10 13 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (10:V)∉mask 111) hin : (10:V)∈eligSet 14 D) miss3
  have miss4 := exposed_exact h hc z (mask 6789) (mask 4757) (by decide +kernel) (by decide +kernel) 3 11 9 (eq ▸ (by decide +kernel : (3:V)∈mask 111)) (by decide +kernel)
  have h4 := code_diff h hc b hb f 11 9 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (11:V)∉mask 111) hin : (11:V)∈eligSet 14 D) miss4 (share h hc (i:=6) (x:=11) (y:=9) (eq ▸ (by decide +kernel : (6:V)∈mask 111)) (by decide +kernel) (by decide +kernel))
  have miss5 := two_exact h hc z (mask 7174) (by decide +kernel) 3 6 11 10 12 (eq ▸ (by decide +kernel : (3:V)∈mask 111)) (eq ▸ (by decide +kernel : (6:V)∈mask 111)) (by decide +kernel)
  have h5 := code_excludes h hc b hb f 11 10 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (11:V)∉mask 111) hin : (11:V)∈eligSet 14 D) miss5
  have miss6 := two_exact h hc z (mask 10401) (by decide +kernel) 3 6 11 13 7 (eq ▸ (by decide +kernel : (3:V)∈mask 111)) (eq ▸ (by decide +kernel : (6:V)∈mask 111)) (by decide +kernel)
  have h6 := code_excludes h hc b hb f 11 13 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (11:V)∉mask 111) hin : (11:V)∈eligSet 14 D) miss6
  have miss7 := exposed_exact h hc z (mask 9992) (mask 792) (by decide +kernel) (by decide +kernel) 2 13 9 (eq ▸ (by decide +kernel : (2:V)∈mask 111)) (by decide +kernel)
  have h7 := code_diff h hc b hb f 13 9 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (13:V)∉mask 111) hin : (13:V)∈eligSet 14 D) miss7 (share h hc (i:=1) (x:=13) (y:=9) (eq ▸ (by decide +kernel : (1:V)∈mask 111)) (by decide +kernel) (by decide +kernel))
  have miss8 := two_exact h hc z (mask 9992) (by decide +kernel) 1 2 13 10 9 (eq ▸ (by decide +kernel : (1:V)∈mask 111)) (eq ▸ (by decide +kernel : (2:V)∈mask 111)) (by decide +kernel)
  have h8 := code_excludes h hc b hb f 13 10 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (13:V)∉mask 111) hin : (13:V)∈eligSet 14 D) miss8
  have miss9 := two_exact h hc z (mask 10401) (by decide +kernel) 1 2 13 11 7 (eq ▸ (by decide +kernel : (1:V)∈mask 111)) (eq ▸ (by decide +kernel : (2:V)∈mask 111)) (by decide +kernel)
  have h9 := code_excludes h hc b hb f 13 11 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (13:V)∉mask 111) hin : (13:V)∈eligSet 14 D) miss9
  have impossible : ∀ a9 a10 a11 a13 : Finset (Fin 3), (¬ a9⊆a11) → (¬ a9⊆a13) → (¬ a10⊆a9) → (a10=∅ ∨ ¬ a10⊆a13) → (¬ a11⊆a9) → (a11=∅ ∨ ¬ a11⊆a10) → (a11=∅ ∨ ¬ a11⊆a13) → (¬ a13⊆a9) → (a13=∅ ∨ ¬ a13⊆a10) → (a13=∅ ∨ ¬ a13⊆a11) → False := by decide +kernel
  exact impossible (code f 9) (code f 10) (code f 11) (code f 13) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 8192 in
theorem residual_exclude4757 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 4757=ineligSet 14 D) : False := by
  classical
  obtain ⟨b,hb⟩ := sem_exists_pureBranch graph_ok h.1 hc
  have card := card_residual h.1 b hb
  have el := inelig_card_add 14 D
  rw [←eq] at el
  have count : (mask 4757).card=6 := by decide +kernel
  have res : Fintype.card ↥(residualUnits 14 D b)=3 := by rw [Fintype.card_coe]; omega
  let f := (Fintype.equivFinOfCardEq res).symm
  have miss0 := exposed_exact h hc z (mask 127) (mask 2087) (by decide +kernel) (by decide +kernel) 7 3 5 (eq ▸ (by decide +kernel : (7:V)∈mask 4757)) (by decide +kernel)
  have h0 := code_diff h hc b hb f 3 5 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (3:V)∉mask 4757) hin : (3:V)∈eligSet 14 D) miss0 (share h hc (i:=12) (x:=3) (y:=5) (eq ▸ (by decide +kernel : (12:V)∈mask 4757)) (by decide +kernel) (by decide +kernel))
  have miss1 := two_exact h hc z (mask 8297) (by decide +kernel) 12 7 3 13 5 (eq ▸ (by decide +kernel : (12:V)∈mask 4757)) (eq ▸ (by decide +kernel : (7:V)∈mask 4757)) (by decide +kernel)
  have h1 := code_excludes h hc b hb f 3 13 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (3:V)∉mask 4757) hin : (3:V)∈eligSet 14 D) miss1
  have miss2 := exposed_exact h hc z (mask 127) (mask 1102) (by decide +kernel) (by decide +kernel) 9 5 3 (eq ▸ (by decide +kernel : (9:V)∈mask 4757)) (by decide +kernel)
  have h2 := code_diff h hc b hb f 5 3 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (5:V)∉mask 4757) hin : (5:V)∈eligSet 14 D) miss2 (share h hc (i:=12) (x:=5) (y:=3) (eq ▸ (by decide +kernel : (12:V)∈mask 4757)) (by decide +kernel) (by decide +kernel))
  have miss3 := two_exact h hc z (mask 314) (by decide +kernel) 9 12 5 8 1 (eq ▸ (by decide +kernel : (9:V)∈mask 4757)) (eq ▸ (by decide +kernel : (12:V)∈mask 4757)) (by decide +kernel)
  have h3 := code_excludes h hc b hb f 5 8 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (5:V)∉mask 4757) hin : (5:V)∈eligSet 14 D) miss3
  have miss4 := two_exact h hc z (mask 8297) (by decide +kernel) 9 12 5 13 6 (eq ▸ (by decide +kernel : (9:V)∈mask 4757)) (eq ▸ (by decide +kernel : (12:V)∈mask 4757)) (by decide +kernel)
  have h4 := code_excludes h hc b hb f 5 13 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (5:V)∉mask 4757) hin : (5:V)∈eligSet 14 D) miss4
  have miss5 := two_exact h hc z (mask 1290) (by decide +kernel) 0 2 8 3 10 (eq ▸ (by decide +kernel : (0:V)∈mask 4757)) (eq ▸ (by decide +kernel : (2:V)∈mask 4757)) (by decide +kernel)
  have h5 := code_excludes h hc b hb f 8 3 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (8:V)∉mask 4757) hin : (8:V)∈eligSet 14 D) miss5
  have miss6 := exposed_exact h hc z (mask 9992) (mask 9288) (by decide +kernel) (by decide +kernel) 0 8 13 (eq ▸ (by decide +kernel : (0:V)∈mask 4757)) (by decide +kernel)
  have h6 := code_diff h hc b hb f 8 13 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (8:V)∉mask 4757) hin : (8:V)∈eligSet 14 D) miss6 (share h hc (i:=2) (x:=8) (y:=13) (eq ▸ (by decide +kernel : (2:V)∈mask 4757)) (by decide +kernel) (by decide +kernel))
  have miss7 := two_exact h hc z (mask 8488) (by decide +kernel) 2 4 13 3 8 (eq ▸ (by decide +kernel : (2:V)∈mask 4757)) (eq ▸ (by decide +kernel : (4:V)∈mask 4757)) (by decide +kernel)
  have h7 := code_excludes h hc b hb f 13 3 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (13:V)∉mask 4757) hin : (13:V)∈eligSet 14 D) miss7
  have miss8 := two_exact h hc z (mask 8488) (by decide +kernel) 2 4 13 5 8 (eq ▸ (by decide +kernel : (2:V)∈mask 4757)) (eq ▸ (by decide +kernel : (4:V)∈mask 4757)) (by decide +kernel)
  have h8 := code_excludes h hc b hb f 13 5 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (13:V)∉mask 4757) hin : (13:V)∈eligSet 14 D) miss8
  have miss9 := exposed_exact h hc z (mask 9992) (mask 1290) (by decide +kernel) (by decide +kernel) 4 13 8 (eq ▸ (by decide +kernel : (4:V)∈mask 4757)) (by decide +kernel)
  have h9 := code_diff h hc b hb f 13 8 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (13:V)∉mask 4757) hin : (13:V)∈eligSet 14 D) miss9 (share h hc (i:=2) (x:=13) (y:=8) (eq ▸ (by decide +kernel : (2:V)∈mask 4757)) (by decide +kernel) (by decide +kernel))
  have impossible : ∀ a3 a5 a8 a13 : Finset (Fin 3), (¬ a3⊆a5) → (a3=∅ ∨ ¬ a3⊆a13) → (¬ a5⊆a3) → (a5=∅ ∨ ¬ a5⊆a8) → (a5=∅ ∨ ¬ a5⊆a13) → (a8=∅ ∨ ¬ a8⊆a3) → (¬ a8⊆a13) → (a13=∅ ∨ ¬ a13⊆a3) → (a13=∅ ∨ ¬ a13⊆a5) → (¬ a13⊆a8) → False := by decide +kernel
  exact impossible (code f 3) (code f 5) (code f 8) (code f 13) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 8192 in
theorem residual_exclude2213 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 2213=ineligSet 14 D) : False := by
  classical
  obtain ⟨b,hb⟩ := sem_exists_pureBranch graph_ok h.1 hc
  have card := card_residual h.1 b hb
  have el := inelig_card_add 14 D
  rw [←eq] at el
  have count : (mask 2213).card=5 := by decide +kernel
  have res : Fintype.card ↥(residualUnits 14 D b)=2 := by rw [Fintype.card_coe]; omega
  let f := (Fintype.equivFinOfCardEq res).symm
  have miss0 := exposed_exact h hc z (mask 127) (mask 4183) (by decide +kernel) (by decide +kernel) 7 3 6 (eq ▸ (by decide +kernel : (7:V)∈mask 2213)) (by decide +kernel)
  have h0 := code_diff h hc b hb f 3 6 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (3:V)∉mask 2213) hin : (3:V)∈eligSet 14 D) miss0 (share h hc (i:=11) (x:=3) (y:=6) (eq ▸ (by decide +kernel : (11:V)∈mask 2213)) (by decide +kernel) (by decide +kernel))
  have miss1 := two_exact h hc z (mask 1290) (by decide +kernel) 0 2 8 3 10 (eq ▸ (by decide +kernel : (0:V)∈mask 2213)) (eq ▸ (by decide +kernel : (2:V)∈mask 2213)) (by decide +kernel)
  have h1 := code_excludes h hc b hb f 8 3 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (8:V)∉mask 2213) hin : (8:V)∈eligSet 14 D) miss1
  have miss2 := exposed_exact h hc z (mask 9992) (mask 9288) (by decide +kernel) (by decide +kernel) 2 8 10 (eq ▸ (by decide +kernel : (2:V)∈mask 2213)) (by decide +kernel)
  have h2 := code_diff h hc b hb f 8 10 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (8:V)∉mask 2213) hin : (8:V)∈eligSet 14 D) miss2 (share h hc (i:=0) (x:=8) (y:=10) (eq ▸ (by decide +kernel : (0:V)∈mask 2213)) (by decide +kernel) (by decide +kernel))
  have miss3 := two_exact h hc z (mask 1290) (by decide +kernel) 0 5 10 3 8 (eq ▸ (by decide +kernel : (0:V)∈mask 2213)) (eq ▸ (by decide +kernel : (5:V)∈mask 2213)) (by decide +kernel)
  have h3 := code_excludes h hc b hb f 10 3 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (10:V)∉mask 2213) hin : (10:V)∈eligSet 14 D) miss3
  have miss4 := exposed_exact h hc z (mask 7426) (mask 4370) (by decide +kernel) (by decide +kernel) 5 10 8 (eq ▸ (by decide +kernel : (5:V)∈mask 2213)) (by decide +kernel)
  have h4 := code_diff h hc b hb f 10 8 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (10:V)∉mask 2213) hin : (10:V)∈eligSet 14 D) miss4 (share h hc (i:=0) (x:=10) (y:=8) (eq ▸ (by decide +kernel : (0:V)∈mask 2213)) (by decide +kernel) (by decide +kernel))
  have impossible : ∀ a3 a6 a8 a10 : Finset (Fin 2), (¬ a3⊆a6) → (a8=∅ ∨ ¬ a8⊆a3) → (¬ a8⊆a10) → (a10=∅ ∨ ¬ a10⊆a3) → (¬ a10⊆a8) → False := by decide +kernel
  exact impossible (code f 3) (code f 6) (code f 8) (code f 10) h0 h1 h2 h3 h4

end PEqualNP.Outside.L_meta_9775.UpstreamCore
