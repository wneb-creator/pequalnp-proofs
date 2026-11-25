import AlgebraicM9Full
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Lean Elab Command
namespace PilotSourceAudit
partial def visit (find : Name → Option ConstantInfo) (n : Name) : StateM NameSet Unit := do
  if !(`PEqualNP.Outside.L_meta_6659_aux).isPrefixOf n then return
  if (← get).contains n then return
  modify fun s => s.insert n
  match find n with
  | none => pure ()
  | some ci => for c in ci.getUsedConstantsAsSet do visit find c
end PilotSourceAudit
run_cmd do
  let env ← getEnv
  let (_, seen) := (PilotSourceAudit.visit env.find? `PEqualNP.Outside.L_meta_6659_aux.equality_p9_mixed_impossible).run {}
  for n in seen do logInfo m!"NEEDED {n}"
