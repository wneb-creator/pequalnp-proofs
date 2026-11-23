import MetadataReplayTest
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
