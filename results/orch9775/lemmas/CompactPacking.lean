import PairedExactFramework

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact

def packedMasks : List Nat := [127,245,314,432,541,792,1102,1290,1548,2087,2213,2338,4183,4309,4370,4757,5008,5190,5316,6151,6789,7174,7426,7812,8297,8417,8488,8713,9288,9992,10401,10656,12481,13504,14977,16256]

def field (n i : Nat) := (n >>> (5+6*i)) &&& 63

def readPackedFact (n : Nat) : Fact :=
  match n%32 with
  | 0 => .live (Fin.ofNat 14 (field n 0)) (field n 1)
  | 1 => .lab (Fin.ofNat 14 (field n 0)) (field n 1) (Fin.ofNat 14 (field n 2))
  | 2 => .res (field n 0) (Fin.ofNat 14 (field n 1))
  | 3 => .common (Fin.ofNat 14 (field n 0)) (Fin.ofNat 14 (field n 1))
  | 4 => .gate (Fin.ofNat 19 (field n 0)) (Fin.ofNat 19 (field n 1))
  | 5 => .reader (field n 0==1) (Fin.ofNat 19 (field n 1)) (field n 2)
  | 6 => .es (field n 0==1) (Fin.ofNat 19 (field n 1)) (Fin.ofNat 14 (field n 2))
  | 7 => .avoid (Fin.ofNat 14 (field n 0)) (packedMasks.getD (field n 1) 0) (field n 2)
  | 8 => .see (Fin.ofNat 14 (field n 0)) (Fin.ofNat 14 (field n 1)) (packedMasks.getD (field n 2) 0) (field n 3)
  | 9 => .diff (field n 0) (Fin.ofNat 14 (field n 1)) (Fin.ofNat 14 (field n 2))
  | _ => default

def readPackedScheme (n : Nat) : Scheme :=
  match n%32 with
  | 0 => .self (Fin.ofNat 14 (field n 0)) (field n 1)
  | 1 => .earlier (Fin.ofNat 14 (field n 0)) (field n 1)
  | 2 => .labCommon (Fin.ofNat 14 (field n 0)) (Fin.ofNat 14 (field n 1)) (field n 2)
  | 3 => .someRes (Fin.ofNat 14 (field n 0))
  | 4 => .allRes (Fin.ofNat 14 (field n 0)) (field n 1)
  | 5 => .exposure (Fin.ofNat 14 (field n 0)) (packedMasks.getD (field n 1) 0)
  | 6 => .exactAt (Fin.ofNat 14 (field n 0)) (Fin.ofNat 14 (field n 1)) (packedMasks.getD (field n 2) 0)
  | 7 => .avoidLive (Fin.ofNat 14 (field n 0)) (packedMasks.getD (field n 1) 0) (field n 2)
  | 8 => .seeLive (Fin.ofNat 14 (field n 0)) (Fin.ofNat 14 (field n 1)) (packedMasks.getD (field n 2) 0) (field n 3)
  | 9 => .avoidNot (Fin.ofNat 14 (field n 0)) (Fin.ofNat 14 (field n 1)) (packedMasks.getD (field n 2) 0) (field n 3)
  | 10 => .seeLab (Fin.ofNat 14 (field n 0)) (Fin.ofNat 14 (field n 1)) (Fin.ofNat 14 (field n 2)) (packedMasks.getD (field n 3) 0) (field n 4)
  | 11 => .diffX (field n 0) (Fin.ofNat 14 (field n 1)) (Fin.ofNat 14 (field n 2))
  | 12 => .diffC (field n 0) (Fin.ofNat 14 (field n 1)) (Fin.ofNat 14 (field n 2))
  | 13 => .adjacentCommon (Fin.ofNat 14 (field n 0)) (Fin.ofNat 14 (field n 1)) (Fin.ofNat 14 (field n 2))
  | 14 => .resCommon (Fin.ofNat 14 (field n 0)) (Fin.ofNat 14 (field n 1)) (field n 2)
  | 15 => .residual (Fin.ofNat 14 (field n 0)) (Fin.ofNat 14 (field n 1)) (field n 2) (field n 3)
  | 16 => .readerAny (field n 0==1) (Fin.ofNat 19 (field n 1))
  | 17 => .readerLive (field n 0==1) (Fin.ofNat 19 (field n 1)) (field n 2)
  | 18 => .readerLab (field n 0==1) (Fin.ofNat 19 (field n 1)) (field n 2) (Fin.ofNat 14 (field n 3)) (field n 4==1)
  | 19 => .eqLab (field n 0==1) (Fin.ofNat 19 (field n 1)) (Fin.ofNat 19 (field n 2)) (Fin.ofNat 14 (field n 3)) (field n 4==1)
  | 20 => .gateEq (field n 0==1) (Fin.ofNat 19 (field n 1)) (Fin.ofNat 19 (field n 2)) (field n 3)
  | _ => default

def readPackedBudget (n : Nat) : BudgetScheme :=
  if n%32=21 then
    .pairedExact (Fin.ofNat 14 (field n 0)) (Fin.ofNat 14 (field n 1))
      (Fin.ofNat 14 (field n 2)) (Fin.ofNat 14 (field n 3)) (packedMasks.getD (field n 4) 0)
  else .plain (readPackedScheme n)

end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
