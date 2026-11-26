import SameSet

namespace PEqualNP.Outside.L_meta_2373_aux.Cert18
open PEqualNP.Outside.L_meta_6581

namespace CollisionProfile
abbrev Profile := Pair × List Word

def support (parent : List Word) (p : Pair) : List Word :=
  parent.filter fun w => Extended.bit p.1 w != Extended.bit p.2 w

def prepare (parent : List Word) (pairs : List Pair) : List Profile :=
  (pairs.filter fun p => Extended.bit p.1 Extended.target != Extended.bit p.2 Extended.target).map
    fun p => (p,support parent p)

def Valid (parent : List Word) (p : Profile) : Prop :=
  (Extended.bit p.1.1 Extended.target != Extended.bit p.1.2 Extended.target) = true ∧
    p.2 = support parent p.1

lemma prepare_valid {parent : List Word} {pairs : List Pair} {p : Profile}
    (mem : p ∈ prepare parent pairs) : Valid parent p := by
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp mem
  exact ⟨(List.mem_filter.mp hp).2,rfl⟩

def cut (p : Profile) (z : Word) (rest : List Word) : Bool :=
  (Extended.bit p.1.1 z == Extended.bit p.1.2 z) &&
    p.2.all (fun w => !(rest.contains w))

lemma cut_sound {parent : List Word} {p : Profile} {z : Word} {rest : List Word}
    (valid : Valid parent p) (sub : ∀ a ∈ rest, a ∈ parent)
    (h : cut p z rest = true) :
    collisionCheck Extended.target p.1.1 p.1.2 (z::rest) = true := by
  have hc : (Extended.bit p.1.1 z == Extended.bit p.1.2 z) = true ∧
      p.2.all (fun w => !(rest.contains w)) = true := by
    simpa only [cut,Bool.and_eq_true] using h
  simp only [collisionCheck,Bool.and_eq_true,List.all_eq_true]
  refine ⟨valid.1,?_⟩
  intro a ha
  rcases List.mem_cons.mp ha with rfl | ha
  · exact hc.1
  · apply beq_iff_eq.mpr
    by_contra diff
    have hm : a ∈ p.2 := by
      rw [valid.2]
      exact List.mem_filter.mpr ⟨sub a ha,bne_iff_ne.mpr diff⟩
    have hn := List.all_eq_true.mp hc.2 a hm
    simp [List.contains_eq_mem,ha] at hn

def check (parent : List Word) (profiles : List Profile) (ws : List Word) : Bool :=
  match ws with
  | [] => false
  | z::rest => rest.all parent.contains && profiles.any (fun p => cut p z rest)

lemma check_sound {parent : List Word} {pairs : List Pair} {ws : List Word}
    (h : check parent (prepare parent pairs) ws = true) (cap : Nat) :
    Impossible Extended.target cap ws := by
  cases ws with
  | nil => simp [check] at h
  | cons z rest =>
    simp only [check,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,
      decide_eq_true_eq,List.any_eq_true] at h
    obtain ⟨sub,p,hp,hcut⟩ := h
    exact collisionCheck_sound (cut_sound (prepare_valid hp) sub hcut) cap

end CollisionProfile

def preparedOracleProfile (parent : List Word) (pools : List Projection.BoundPool)
    (pairs : List Pair) (links : List PreparedLink)
    (k : Nat) (ws : List Word) (op : Choice) : Bool :=
  CollisionProfile.check parent (CollisionProfile.prepare parent pairs) ws ||
  pools.any (fun c => cutCheckFast c k ws op) ||
  preparedLinkCheckFast links k ws

lemma preparedOracleProfile_sound {parent : List Word} {pools : List Projection.BoundPool}
    {pairs : List Pair} {links : List PreparedLink}
    (pool_ok : ∀ c ∈ pools, Projection.ValidPool true Extended.initial Extended.target c)
    (links_ok : ∀ l ∈ links, Impossible Extended.target l.1 l.2)
    {k ws op} (checked : preparedOracleProfile parent pools pairs links k ws op = true) :
    Impossible Extended.target k ws := by
  simp only [preparedOracleProfile,Bool.or_eq_true,List.any_eq_true] at checked
  rcases checked with (collision | ⟨c,hc,cut⟩) | link
  · exact CollisionProfile.check_sound collision k
  · rw [cutCheckFast_eq] at cut
    exact Projection.cutCheck_sound (pool_ok c hc) cut
  · exact preparedLinkCheckFast_sound links_ok link

end PEqualNP.Outside.L_meta_2373_aux.Cert18
