import UpstreamGraph

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore

open DagTools

def auto (σ : Equiv.Perm V) := ∀ i j, adj (σ i) (σ j) ↔ adj i j

set_option maxHeartbeats 0 in
theorem rename {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (σ : Equiv.Perm V) (a : auto σ) :
    sem_Comp 14 adj (relabel σ D) := by
  intro x
  rw [relabel_out σ h.1 h.2.2,hc]
  constructor
  · rintro ⟨u,v,uv,hu,hv⟩; exact ⟨σ u,σ v,(a _ _).2 uv,hu,hv⟩
  · rintro ⟨u,v,uv,hu,hv⟩
    refine ⟨σ.symm u,σ.symm v,(a _ _).1 (by simpa using uv),by simpa using hu,by simpa using hv⟩

def permFn0 (v : V) : V := ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] : List V)[v.val]!

def graphPerm0 : Equiv.Perm V where
  toFun := permFn0
  invFun := permFn0
  left_inv := by decide +kernel
  right_inv := by decide +kernel

set_option maxHeartbeats 0 in
theorem auto0 : auto graphPerm0 := by unfold auto; decide +kernel

def permFn1 (v : V) : V := ([2, 5, 0, 3, 4, 1, 6, 12, 8, 9, 13, 11, 7, 10] : List V)[v.val]!

def graphPerm1 : Equiv.Perm V where
  toFun := permFn1
  invFun := permFn1
  left_inv := by decide +kernel
  right_inv := by decide +kernel

set_option maxHeartbeats 0 in
theorem auto1 : auto graphPerm1 := by unfold auto; decide +kernel

def permFn2 (v : V) : V := ([7, 10, 12, 8, 9, 13, 11, 0, 3, 4, 1, 6, 2, 5] : List V)[v.val]!

def graphPerm2 : Equiv.Perm V where
  toFun := permFn2
  invFun := permFn2
  left_inv := by decide +kernel
  right_inv := by decide +kernel

set_option maxHeartbeats 0 in
theorem auto2 : auto graphPerm2 := by unfold auto; decide +kernel

def permFn3 (v : V) : V := ([12, 13, 7, 8, 9, 10, 11, 2, 3, 4, 5, 6, 0, 1] : List V)[v.val]!

def graphPerm3 : Equiv.Perm V where
  toFun := permFn3
  invFun := permFn3
  left_inv := by decide +kernel
  right_inv := by decide +kernel

set_option maxHeartbeats 0 in
theorem auto3 : auto graphPerm3 := by unfold auto; decide +kernel

set_option maxHeartbeats 0 in
theorem move_case {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (len : D.length≤24)
    (i j : Nat) (eq : mask i=ineligSet 14 D) (σ : Equiv.Perm V) (a : auto σ) (moved : (mask i).image σ=mask j) :
    ∃ E : Dag, StrictLive 14 E ∧ sem_Comp 14 adj E ∧ E.length≤24 ∧ ineligSet 14 E=mask j := by
  refine ⟨relabel σ D,relabel_strictLive σ h,rename h hc σ a,by simpa [relabel_length] using len,?_⟩
  rw [relabel_ineligSet σ h.1,←eq,moved]

end PEqualNP.Outside.L_meta_9775.UpstreamCore
