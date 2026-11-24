import ProjectedChildTest
namespace PEqualNP.Outside.L_meta_670_aux.MetadataMarker

open LiveCheck MetadataReplay

def terminal (c : Config) (level k t j : Nat) (v : List Sig) : Bool :=
  decide (k = level) && decide (j < c.count k t) && c.enabled k t j &&
    v.isPerm (c.state k t j)

lemma terminal_sound (c : Config) (level : Nat)
    (leaves : ∀ t j, j < c.count level t → c.enabled level t j = true →
      Impossible level t (c.state level t j))
    (k t j : Nat) (v : List Sig) (h : terminal c level k t j v = true) :
    Impossible k t v := by
  simp only [terminal,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at h
  obtain ⟨⟨⟨hk,hj⟩,he⟩,hp⟩ := h
  subst k
  have hi := leaves t j hj he
  have hv : v.toFinset = (c.state level t j).toFinset := by
    ext a
    simpa only [List.mem_toFinset] using hp.mem_iff
  intro m hm hl
  apply hi m hm
  rw [← hv]
  exact hl

def config (c : Config) (level : Nat) : Config := { c with terminal := terminal c level }

lemma config_valid (c : Config) (hc : Valid c) (level : Nat)
    (leaves : ∀ t j, j < c.count level t → c.enabled level t j = true →
      Impossible level t (c.state level t j)) : Valid (config c level) :=
  ⟨hc.transport,terminal_sound c level leaves,hc.cuts⟩

end PEqualNP.Outside.L_meta_670_aux.MetadataMarker

namespace PEqualNP.Outside.L_meta_670_aux.RootSeven
open LiveCheck
def nodes12 : List Nat := [15,165,166,193,344,355,362,696,702,707,891,1111]
def nodes13 : List Nat := [345,379,713,899,1118,1323]
def nodes14 : List Nat := [723,1522]
def nodes15 : List Nat := [1876]

def nodes : Nat → List Nat
  | 12 => nodes12
  | 13 => nodes13
  | 14 => nodes14
  | 15 => nodes15
  | _ => []

def restricted : MetadataReplay.Config :=
  { DiagonalT7.config with enabled := fun k t j =>
      DiagonalT7.config.enabled k t j && (nodes k).contains j }

lemma restricted_valid : MetadataReplay.Valid restricted :=
  ⟨DiagonalT7.config_valid.transport,DiagonalT7.config_valid.terminal,DiagonalT7.config_valid.cuts⟩

def config : MetadataReplay.Config := MetadataMarker.config restricted 12

lemma config_valid
    (leaves : ∀ i : Fin nodes12.length, Impossible 12 4 (Cut12StrictReplay.state 12 4 nodes12[i.val])) :
    MetadataReplay.Valid config := by
  apply MetadataMarker.config_valid restricted restricted_valid 12
  intro t j hj he
  have ht : t = 4 := by
    by_contra hn
    have hne : t+8 ≠ 12 := by omega
    simp only [restricted,DiagonalT7.config,hne,ite_false] at hj
    omega
  subst t
  have hmem : j ∈ nodes12 := by
    simp only [restricted, nodes, Bool.and_eq_true, List.contains_iff_mem] at he
    exact he.2
  obtain ⟨i,hi,heq⟩ := List.getElem_of_mem hmem
  change Impossible 12 4 (Cut12StrictReplay.state 12 4 j)
  simpa only [heq] using leaves ⟨i,hi⟩

end PEqualNP.Outside.L_meta_670_aux.RootSeven
