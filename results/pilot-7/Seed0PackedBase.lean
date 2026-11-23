import Seed0SymBase

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace PEqualNP.Outside.L_meta_982_aux.Finite

def seed0Payload (s i tag : Nat) : Nat :=
  (((seed0Advice s i).toList.find? (fun entry => entry % 1024 == tag)).getD 0) / 1024

def seed0Child (s i tag : Nat) : Nat :=
  let payload := seed0Payload s i tag
  if payload = 0 then seed0Count (s-1) else (payload-1)/64

def seed0Orient (s i tag : Nat) (ws : List Nat) : List Nat :=
  let payload := seed0Payload s i tag
  if payload = 0 then ws
  else ws.map (seed0SymWord ((payload-1)%64))

def seed0Check (s i : Nat) : Bool :=
  Fast.pairedBar seed0Forbidden seed0K seed0ScoreWidth seed0States seed0Count
    seed0Child seed0Orient seed0Pool s i

end PEqualNP.Outside.L_meta_982_aux.Finite
