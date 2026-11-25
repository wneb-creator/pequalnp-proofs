import CheckLemma
import PEqualNP.Outside.R_meta_5324_49

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let some ci := env.find? `PEqualNP.Outside.R_meta_5324_49
    | throwError "theorem missing"
  let .forallE _ first rest _ := ci.type
    | throwError "first hypothesis missing"
  let .forallE _ second _ _ := rest
    | throwError "second hypothesis missing"
  for (i, t) in [(1, first), (2, second)] do
    let printed ← liftIO <| PEqualNPChecker.runMetaIn env do
      let f ← Meta.ppExpr (PEqualNPChecker.canonBinders t)
      return (f.pretty 1000000).replace "\n" " "
    liftIO <| IO.println s!"CHILD {i} LENGTH {printed.length}"
    liftIO <| IO.println printed
    liftIO <| IO.println s!"END CHILD {i}"
