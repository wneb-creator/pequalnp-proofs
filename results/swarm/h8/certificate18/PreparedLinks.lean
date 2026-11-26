import Checker

namespace PEqualNP.Outside.L_meta_2373_aux.Cert18
open PEqualNP.Outside.L_meta_6581

namespace Automorphism

set_option maxRecDepth 4096 in
lemma impossible_preimage {target : Word} {cap : Nat} {ws : List Word}
    (hi : Impossible target cap ws) (p : List Move) (ok : autoOK target p = true) :
    Impossible target cap (ws.map (movedWord p.reverse)) := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) :=
    fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k hk h
  have run := live_rename h (movedRow p) onto
  have goal : rename (movedRow p) target = target :=
    (moved_eq_rename p target).symm.trans ok.1.1
  have inv (x : Word) : rename (movedRow p) (movedWord p.reverse x) = x := by
    apply Extended.bit_ext
    intro r
    rw [bit_rename,bit_moved,composed_id ok.1.2]
  have back : (ws.map (movedWord p.reverse)).toFinset.image (rename (movedRow p)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
      simpa only [inv] using hw
    · intro ha
      exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k hk run

end Automorphism

abbrev PreparedLink := Nat × List Word

def prepareLinks {n : Nat} (states : Fin n → State) (budget : Fin n → Nat)
    (i : Fin n) (links : List (Link n)) : List PreparedLink :=
  (links.filter fun l => decide (budget l.1 < budget i)).map fun l =>
    (budget l.1, (states l.1).live.map (Automorphism.movedWord l.2.reverse))

lemma prepareLinks_sound {n : Nat} {states : Fin n → State} {budget : Fin n → Nat}
    {i : Fin n} {links : List (Link n)}
    (valid : ∀ l ∈ links, Automorphism.autoOK Extended.target l.2 = true)
    (earlier : ∀ j, budget j < budget i → Impossible Extended.target (budget j) (states j).live) :
    ∀ l ∈ prepareLinks states budget i links, Impossible Extended.target l.1 l.2 := by
  intro l hl
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hl
  have hv' := List.mem_filter.mp hv
  exact Automorphism.impossible_preimage (earlier _ (of_decide_eq_true hv'.2)) _ (valid _ hv'.1)

def preparedLinkCheck (links : List PreparedLink) (k : Nat) (ws : List Word) : Bool :=
  links.any fun l => decide (k ≤ l.1 ∧ ws.toFinset = l.2.toFinset)

lemma preparedLinkCheck_sound {links : List PreparedLink} {k : Nat} {ws : List Word}
    (valid : ∀ l ∈ links, Impossible Extended.target l.1 l.2)
    (checked : preparedLinkCheck links k ws = true) : Impossible Extended.target k ws := by
  obtain ⟨l,hl,h⟩ := List.any_eq_true.mp checked
  have h' : k ≤ l.1 ∧ ws.toFinset = l.2.toFinset := of_decide_eq_true h
  intro j hj run
  rw [h'.2] at run
  exact valid l hl j (hj.trans h'.1) run

def preparedOracle (pools : List Projection.BoundPool) (pairs : List Pair)
    (links : List PreparedLink) (k : Nat) (ws : List Word) (op : Choice) : Bool :=
  pairs.any (fun p => collisionCheck Extended.target p.1 p.2 ws) ||
  pools.any (fun c => Projection.cutCheck c k ws op) ||
  preparedLinkCheck links k ws

lemma preparedOracle_sound {pools : List Projection.BoundPool} {pairs : List Pair}
    {links : List PreparedLink}
    (pool_ok : ∀ c ∈ pools, Projection.ValidPool true Extended.initial Extended.target c)
    (links_ok : ∀ l ∈ links, Impossible Extended.target l.1 l.2)
    {k ws op} (checked : preparedOracle pools pairs links k ws op = true) :
    Impossible Extended.target k ws := by
  simp only [preparedOracle,Bool.or_eq_true,List.any_eq_true] at checked
  rcases checked with (⟨p,hp,cut⟩ | ⟨c,hc,cut⟩) | link
  · exact collisionCheck_sound cut k
  · exact Projection.cutCheck_sound (pool_ok c hc) cut
  · exact preparedLinkCheck_sound links_ok link

end PEqualNP.Outside.L_meta_2373_aux.Cert18
