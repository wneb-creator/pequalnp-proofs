import Checker

namespace PEqualNP.Outside.L_meta_2373_aux.Cert18
open PEqualNP.Outside.L_meta_6581

lemma child_flip {ws : List Word} (hn : ws.Nodup) (a b : Word) (d : Nat)
    (hd : d < 4) (ka kb : Bool) :
    (child ws a b d ka kb).toFinset =
      (child ws b a (Extended.flipOp d) kb ka).toFinset := by
  have flip := Extended.bin_flip (u:=true) (Or.inr ⟨rfl,hd⟩) a b
  simp only [child,List.toFinset_cons,kept_fin_word,erase_fin (hn.erase _),erase_fin hn,flip]
  cases ka <;> cases kb <;> ext x <;> simp <;> tauto

lemma child_flip_length (ws : List Word) (a b : Word) (d : Nat) (ka kb : Bool) :
    (child ws a b d ka kb).length =
      (child ws b a (Extended.flipOp d) kb ka).length := by
  cases ka <;> cases kb <;> simp [child,kept,List.erase_comm]

def nodeCheckHalf (target : Word) (oracle : Nat → List Word → Choice → Bool)
    (cap : Nat) (ws : List Word) : Bool :=
  decide ws.Nodup && !(ws.contains target) &&
    ws.all (fun a => ws.all (fun b =>
      if a.toNat < b.toNat then pairCheck oracle cap ws a b else true))

lemma nodeCheckHalf_sound {target : Word} {oracle : Nat → List Word → Choice → Bool}
    {cap : Nat} {ws : List Word}
    (oracle_sound : ∀ k xs op, oracle k xs op = true → Impossible target k xs)
    (checked : nodeCheckHalf target oracle cap ws = true) : Impossible target cap ws := by
  simp only [nodeCheckHalf,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',
    List.contains_eq_mem] at checked
  have out : target ∉ ws := by
    intro ht
    simpa [ht] using checked.1.2
  have one (a : Word) (ha : a ∈ ws) (b : Word) (hb : b ∈ ws) (lt : a.toNat < b.toNat)
      (d : Nat) (hd : d < 4) (ka kb : Bool) (hab : a ≠ b)
      (fresh : Extended.bin d a b ∉ ws) (hz : Extended.proper (Extended.bin d a b))
      (len : (child ws a b d ka kb).length ≤ cap) :
      Impossible target (cap-1) (child ws a b d ka kb) := by
    have pair := List.all_eq_true.mp (List.all_eq_true.mp checked.2 a ha) b hb
    simp only [lt,ite_true] at pair
    have op := List.all_eq_true.mp pair d (List.mem_range.mpr hd)
    have keepa := List.all_eq_true.mp op ka (by cases ka <;> simp)
    have keepb := List.all_eq_true.mp keepa kb (by cases kb <;> simp)
    apply oracle_sound
    simpa [gateCheck,hab,hz.1,hz.2,List.contains_eq_mem,fresh,Nat.not_lt.mpr len] using keepb
  apply enum_step checked.1.1 out
  intro a ha b hb d hd ka kb hab fresh hz len
  by_cases lt : a.toNat < b.toNat
  · exact one a ha b hb lt d hd ka kb hab fresh hz len
  · have neq : a.toNat ≠ b.toNat := fun h => hab (BitVec.eq_of_toNat_eq h)
    have back : b.toNat < a.toNat := by omega
    have flip := Extended.bin_flip (u:=true) (Or.inr ⟨rfl,hd⟩) a b
    have df : Extended.flipOp d < 4 := by
      unfold Extended.flipOp
      split_ifs <;> omega
    have alt := one b hb a ha back (Extended.flipOp d) df kb ka hab.symm
      (flip ▸ fresh) (flip ▸ hz) (by rwa [←child_flip_length])
    intro k hk run
    exact alt k hk ((child_flip checked.1.1 a b d hd ka kb) ▸ run)

end PEqualNP.Outside.L_meta_2373_aux.Cert18
