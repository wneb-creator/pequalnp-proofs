import CompactFramework

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore
open DagTools

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 8192 in
theorem residual_empty4293 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (z : Bzero 14 D=0) (eq : mask 4293=ineligSet 14 D)
    (b : V → Nat) (hb : PureBranch 14 D b)
    (f : Fin 2 ≃ ↥(residualUnits 14 D b)) : code f 5=∅ ∧ code f 10=∅ := by
  classical
  have miss0 := exposed_exact h hc z (mask 127) (mask 2087) (by decide +kernel) (by decide +kernel) 7 3 5 (eq ▸ (by decide +kernel : (7:V)∈mask 4293)) (by decide +kernel)
  have h0 := code_diff h hc b hb f 3 5 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (3:V)∉mask 4293) hin : (3:V)∈eligSet 14 D) miss0 (share h hc (i:=12) (x:=3) (y:=5) (eq ▸ (by decide +kernel : (12:V)∈mask 4293)) (by decide +kernel) (by decide +kernel))
  have miss1 := two_exact h hc z (mask 314) (by decide +kernel) 7 12 3 8 1 (eq ▸ (by decide +kernel : (7:V)∈mask 4293)) (eq ▸ (by decide +kernel : (12:V)∈mask 4293)) (by decide +kernel)
  have h1 := code_excludes h hc b hb f 3 8 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (3:V)∉mask 4293) hin : (3:V)∈eligSet 14 D) miss1
  have miss2 := two_exact h hc z (mask 1102) (by decide +kernel) 7 12 3 10 1 (eq ▸ (by decide +kernel : (7:V)∈mask 4293)) (eq ▸ (by decide +kernel : (12:V)∈mask 4293)) (by decide +kernel)
  have h2 := code_excludes h hc b hb f 3 10 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (3:V)∉mask 4293) hin : (3:V)∈eligSet 14 D) miss2
  have miss3 := exposed_exact h hc z (mask 314) (mask 792) (by decide +kernel) (by decide +kernel) 12 5 8 (eq ▸ (by decide +kernel : (12:V)∈mask 4293)) (by decide +kernel)
  have h3 := code_excludes h hc b hb f 5 8 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (5:V)∉mask 4293) hin : (5:V)∈eligSet 14 D) miss3
  have miss4 := two_exact h hc z (mask 792) (by decide +kernel) 6 0 8 3 9 (eq ▸ (by decide +kernel : (6:V)∈mask 4293)) (eq ▸ (by decide +kernel : (0:V)∈mask 4293)) (by decide +kernel)
  have h4 := code_excludes h hc b hb f 8 3 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (8:V)∉mask 4293) hin : (8:V)∈eligSet 14 D) miss4
  have miss5 := two_exact h hc z (mask 2338) (by decide +kernel) 6 0 8 5 11 (eq ▸ (by decide +kernel : (6:V)∈mask 4293)) (eq ▸ (by decide +kernel : (0:V)∈mask 4293)) (by decide +kernel)
  have h5 := code_excludes h hc b hb f 8 5 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (8:V)∉mask 4293) hin : (8:V)∈eligSet 14 D) miss5
  have miss6 := two_exact h hc z (mask 7426) (by decide +kernel) 6 2 8 10 11 (eq ▸ (by decide +kernel : (6:V)∈mask 4293)) (eq ▸ (by decide +kernel : (2:V)∈mask 4293)) (by decide +kernel)
  have h6 := code_diff h hc b hb f 8 10 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (8:V)∉mask 4293) hin : (8:V)∈eligSet 14 D) miss6 (share h hc (i:=0) (x:=8) (y:=10) (eq ▸ (by decide +kernel : (0:V)∈mask 4293)) (by decide +kernel) (by decide +kernel))
  have miss7 := exposed_exact h hc z (mask 1290) (mask 314) (by decide +kernel) (by decide +kernel) 0 10 3 (eq ▸ (by decide +kernel : (0:V)∈mask 4293)) (by decide +kernel)
  have h7 := code_excludes h hc b hb f 10 3 (by decide +kernel) (by by_contra hx; have hin := sem_mem_inelig.mpr hx; rw [←eq] at hin; exact (by decide +kernel : (10:V)∉mask 4293) hin : (10:V)∈eligSet 14 D) miss7
  have finite : ∀ a3 a5 a8 a10 : Finset (Fin 2), (¬ a3⊆a5) → (a3=∅ ∨ ¬ a3⊆a8) → (a3=∅ ∨ ¬ a3⊆a10) → (a5=∅ ∨ ¬ a5⊆a8) → (a8=∅ ∨ ¬ a8⊆a3) → (a8=∅ ∨ ¬ a8⊆a5) → (¬ a8⊆a10) → (a10=∅ ∨ ¬ a10⊆a3) → a5=∅ ∧ a10=∅ := by decide +kernel
  exact finite (code f 3) (code f 5) (code f 8) (code f 10) h0 h1 h2 h3 h4 h5 h6 h7

end PEqualNP.Outside.L_meta_9775.UpstreamCore
