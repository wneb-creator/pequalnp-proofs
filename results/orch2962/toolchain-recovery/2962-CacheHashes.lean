import Cache.Hashing
open Lean Cache Cache.IO Cache.Hashing
def main : IO Unit := CacheM.run do
  let roots ← parseArgs ["PEqualNP.Defs", "Mathlib.Combinatorics.Hall.Finite"]
  let memo ← getHashMemo roots
  for (mod, hash) in memo.hashMap.toArray do
    IO.println s!"{mod} {hash.asLTar}"
