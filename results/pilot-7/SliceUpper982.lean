import Indexed982
import Slice982
namespace PEqualNP.Outside.L_meta_982_aux.Finite.Reduced
open PEqualNP.Outside.L_meta_982_aux.Finite.Live

def rejectWith (forbidden : List Nat) (m y : Nat) (bad : Nat → List Nat → Bool) :
    Nat → Nat → List Nat → Bool
  | 0,s,ws => if ws == [y] then false else bad s ws
  | d+1,s,ws => if ws == [y] then false else bad s ws ||
      match s with
      | 0 => true
      | s+1 => !(next forbidden m (s+2-ws.length) ws fun _ zs =>
          !(rejectWith forbidden m y bad d s zs))

theorem rejectWith_no {forbidden m y bad} (d : Nat)
    (hbad : ∀ s {t ws}, t ≤ s → RNatRun forbidden m y t ws → bad s ws = false)
    {t s ws} (h : RNatRun forbidden m y t ws) (ht : t ≤ s) :
    rejectWith forbidden m y bad d s ws = false := by
  induction d generalizing t s ws with
  | zero =>
    by_cases hw : ws = [y]
    · simp [rejectWith,hw]
    · simp [rejectWith,hw,hbad s ht h]
  | succ d ih =>
    by_cases hw : ws = [y]
    · simp [rejectWith,hw]
    · cases t with
      | zero => exact False.elim (hw (zero_done h.toRun rfl))
      | succ t =>
        cases s with
        | zero => omega
        | succ s =>
          let F (_ : Nat) (zs : List Nat) : Bool := !(rejectWith forbidden m y bad d s zs)
          have hF (tag : Nat) (zs : List Nat) (hz : RNatRun forbidden m y t zs) :
              F tag zs = true := by simp [F,ih hz (show t ≤ s by omega)]
          have hN := next_complete h t rfl _ (List.Perm.refl _) F hF
          have hN' := next_monoSlack (show t+2-ws.length ≤ s+2-ws.length by omega) hN
          simpa [rejectWith,hw,hbad s.succ ht h,F] using hN'

end PEqualNP.Outside.L_meta_982_aux.Finite.Reduced

namespace PEqualNP.Outside.L_meta_982_aux.Finite.Slice

def bad (k p s : Nat) (ws : List Nat) : Bool := !(Fast.covers k s ws) || scr k p s ws

theorem bad_no {forbidden k p} (hk : 3*p ≤ k) (s : Nat) {t ws} (ht : t ≤ s)
    (h : Reduced.RNatRun forbidden (Live.mask k) (Live.goal k) t ws) :
    bad k p s ws = false := by
  simp [bad,Fast.covers_eq,Reduced.covers_ok_le h.toRun ht,scr_no_le hk h.toRun ht]

abbrev reject (forbidden : List Nat) (k p : Nat) :=
  Reduced.rejectWith forbidden (Live.mask k) (Live.goal k) (bad k p)

theorem reject_no {forbidden k p t s ws} (hk : 3*p ≤ k) (d : Nat)
    (h : Reduced.RNatRun forbidden (Live.mask k) (Live.goal k) t ws) (ht : t ≤ s) :
    reject forbidden k p d s ws = false :=
  Reduced.rejectWith_no d (fun u _ _ hu hh => bad_no hk u hu hh) h ht

end PEqualNP.Outside.L_meta_982_aux.Finite.Slice
