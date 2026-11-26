import PreparedLinks

namespace PEqualNP.Outside.L_meta_2373_aux.Cert18

def sameSetB (xs ys : List Word) : Bool :=
  xs.all ys.contains && ys.all xs.contains

lemma sameSetB_sound {xs ys : List Word} (h : sameSetB xs ys = true) :
    xs.toFinset = ys.toFinset := by
  simp only [sameSetB,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  ext a
  simpa using (show a ∈ xs ↔ a ∈ ys from ⟨fun hm => h.1 a hm,fun hm => h.2 a hm⟩)

def nodupB : List Word → Bool
  | [] => true
  | a::xs => !(xs.contains a) && nodupB xs

lemma nodupB_sound {xs : List Word} (h : nodupB xs = true) : xs.Nodup := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [nodupB,Bool.and_eq_true,Bool.not_eq_true',List.contains_eq_mem] at h
    exact List.nodup_cons.mpr ⟨by simpa using h.1,ih h.2⟩

lemma nodupB_eq_decide (xs : List Word) : nodupB xs = decide xs.Nodup := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [nodupB,List.nodup_cons,ih,List.contains_eq_mem]

def cutCheckFast (c : Projection.BoundPool) (k : Nat) (ws : List Word) (op : Choice) : Bool :=
  match ws with
  | [] => false
  | z::rest => (z == Projection.choiceVal op) && nodupB ws &&
      Projection.scalarPoolCut true c k rest op

lemma cutCheckFast_eq (c : Projection.BoundPool) (k : Nat) (ws : List Word) (op : Choice) :
    cutCheckFast c k ws op = Projection.cutCheck c k ws op := by
  cases ws <;> simp only [cutCheckFast,Projection.cutCheck,nodupB_eq_decide]

def preparedLinkCheckFast (links : List PreparedLink) (k : Nat) (ws : List Word) : Bool :=
  links.any fun l => decide (k ≤ l.1) && sameSetB ws l.2

lemma preparedLinkCheckFast_sound {links : List PreparedLink} {k : Nat} {ws : List Word}
    (valid : ∀ l ∈ links, Impossible PEqualNP.Outside.L_meta_6581.Extended.target l.1 l.2)
    (checked : preparedLinkCheckFast links k ws = true) :
    Impossible PEqualNP.Outside.L_meta_6581.Extended.target k ws := by
  obtain ⟨l,hl,h⟩ := List.any_eq_true.mp checked
  have h' : decide (k ≤ l.1) = true ∧ sameSetB ws l.2 = true := by
    simpa only [Bool.and_eq_true] using h
  have kb : k ≤ l.1 := of_decide_eq_true h'.1
  have eq := sameSetB_sound h'.2
  intro j hj run
  rw [eq] at run
  exact valid l hl j (hj.trans kb) run

open PEqualNP.Outside.L_meta_6581

def preparedOracleFast (pools : List Projection.BoundPool) (pairs : List Pair)
    (links : List PreparedLink) (k : Nat) (ws : List Word) (op : Choice) : Bool :=
  pairs.any (fun p => collisionCheck Extended.target p.1 p.2 ws) ||
  pools.any (fun c => cutCheckFast c k ws op) ||
  preparedLinkCheckFast links k ws

lemma preparedOracleFast_sound {pools : List Projection.BoundPool} {pairs : List Pair}
    {links : List PreparedLink}
    (pool_ok : ∀ c ∈ pools, Projection.ValidPool true Extended.initial Extended.target c)
    (links_ok : ∀ l ∈ links, Impossible Extended.target l.1 l.2)
    {k ws op} (checked : preparedOracleFast pools pairs links k ws op = true) :
    Impossible Extended.target k ws := by
  simp only [preparedOracleFast,Bool.or_eq_true,List.any_eq_true] at checked
  rcases checked with (⟨p,hp,cut⟩ | ⟨c,hc,cut⟩) | link
  · exact collisionCheck_sound cut k
  · rw [cutCheckFast_eq] at cut
    exact Projection.cutCheck_sound (pool_ok c hc) cut
  · exact preparedLinkCheckFast_sound links_ok link


end PEqualNP.Outside.L_meta_2373_aux.Cert18
