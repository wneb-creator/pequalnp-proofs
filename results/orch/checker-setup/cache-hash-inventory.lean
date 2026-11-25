import Cache.Hashing
open Lean Cache.IO Cache.Hashing

def main : IO Unit := CacheM.run do
  let memo ← getHashMemo {}
  let sp := (← read).srcSearchPath
  for (mod, hash) in memo.hashMap.toArray do
    let source ← Lean.findLean sp mod
    IO.println s!"{mod}\t{hash.toNat}\t{source}"
