import OwnSequence
namespace PEqualNP.Outside.L_meta_10760_first
def ownRows (raw : List (Nat × Nat)) (cs : List Nat) : List ((Nat × Nat) × List Nat) :=
  cs.filterMap fun c => (raw.find? fun x => Nat.beq x.1 c).map fun x =>
    (x, (pr raw c).map Prod.fst)
end PEqualNP.Outside.L_meta_10760_first
