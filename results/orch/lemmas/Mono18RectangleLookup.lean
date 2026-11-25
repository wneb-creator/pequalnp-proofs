import Mono18RectangleCosts

namespace PEqualNP.Outside.L_meta_2373.Mono18Rectangle

abbrev Record := {p : Nat × Nat // checkRecord p.1 p.2 = true}

def zeroRecord : Record := ⟨(0, 0), by decide +kernel⟩
def emptyBlock : Block := ⟨0, ⟨[], rfl⟩⟩

def blockRecords (b : Block) : List Record :=
  b.2.val.attach.map (fun r => ⟨(b.1, r.val), block_valid b r.val r.property⟩)

def certifiedAt (blockIndex recordIndex : Nat) : Record :=
  (blockRecords (blocks.getD blockIndex emptyBlock)).getD recordIndex zeroRecord

lemma certifiedAt_valid (blockIndex recordIndex : Nat) :
    checkRecord (certifiedAt blockIndex recordIndex).val.1
      (certifiedAt blockIndex recordIndex).val.2 = true :=
  (certifiedAt blockIndex recordIndex).property

end PEqualNP.Outside.L_meta_2373.Mono18Rectangle
