import CompactPacking

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.Outside.L_meta_9775.UpstreamCore.Resolution

def aP416 := ([0x120101,0x160101,0x2107,0x4907,0x120121,0x920,0x140121,0x5123,0x160121,0x180121,0x120921,0x140921,0x160921,0x180921,0x8927,0x28927,0x9927,0x29927,0xa927,0x2a927,0x282928,0xa82928,0x160161,0x160961,0x8005,0x28005,0x8805,0x28805,0x9005,0x29005,0x8025,0x128026,0x168026,0x8825,0x28825,0x128826,0x168826,0x9025,0x29025,0x169026,0x8a04,0x9204,0x9224] : List Nat).toArray.map readPackedFact
def rP416 := ([0x2105,0x84909,0x4905,0x125909,288,0x920,0x8925,0x226129,0xa25129,0x9925,0x265929,0xa66129,0xa925,0x2a5129,0xaa5929,0x282926,0xa16292a,0xa18292a,0x2a16292a,0x2a18292a,0xa512d,0x80512f,352,0x960,0x8010,0x8810,0x9010,0x8030,0x4808032,0x5808032,0x8830,0x24808832,0x5808832,0x28831,0x24828832,0x5828832,0x9030,0x25809032,0x25829032,0x228014,0xa28014,0x4a28033,0x248014,0xa48014,0x5a48033,0x248814,0xa48814,0x5a48833] : List Nat).map readPackedScheme

def tableP416_0 : List Nat := [321,258,449,0x4182,577,0x541,0x3e742,0x24702,0x2c782,0x46842,0x20802,0x34882,0x4e942,0x18902,0x30982,0x56a42]
def tableP416_1 : List Nat := [0x20a02,0x26a02,0x30a82,0x36a82,961,0xb8d14384,0xb41,0xbc1,0x66c42,0x6ed42,0x76e42,0xf41,0x3e02f03,0x4006f03,0x8b0c2,0x4711083]
def tableP416_2 : List Nat := [0x4823083,0x17102,0x4729103,0x4833103,0x9b2c2,0x4f59283,0x4f5d303,0x5168c03,0x516cc83,0x467f403,0x5370c03,0x5374c83,0x4e83483,0x5570d03,0x5574d83,0x4e93503]
def tableP416_3 : List Nat := [1,129,0x171a283,0xf81,0x1001,0x8f082,0x8f102,0x9f282,0x9f302,0x8d402,0x9d482,0x13c1,0x1481,0x11c1,0x1401,0x401]
def tableP416_4 : List Nat := [0x1201,0x1501,0xe81,0xe41,0xc01,0xd01,0xcc1,0xdc1]

def encodedP416 (i : Nat) : Nat :=
  if i < 32 then
    if i < 16 then
      tableP416_0.getD (i%16) 0
    else
      tableP416_1.getD (i%16) 0
  else
    if i < 48 then
      tableP416_2.getD (i%16) 0
    else
      if i < 64 then
        tableP416_3.getD (i%16) 0
      else
        tableP416_4.getD (i%16) 0
def bookP416 (i : Nat) : Clause := let n := encodedP416 i; unpackLits 7 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClausesP416 : inputsOK 0 416 aP416 rP416 (baseBook bookP416 48).toList=true := by decide +kernel

def rowsP416_0 : List Nat := [513,0x20601,0x142a01,0x181b3802,0x189b3a02,0x43e01,0x54401,0x164a01,0x174c01,0x335201,0x345801,0x1c374802,0x3b7401,0x1b353c02,0x3d7201,0xb1e2480a2605,0x407644468f1848723427903f0c0e,0x1dc05e02,0x64c2e56fa0bc4e07,0x423401,0x1e435402,0x20c35a02,0x443001,0x453201]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOkP416_0 : checkRows bookP416 7 48 rowsP416_0=true := by decide +kernel

def lastUnitsP416 := digits 7 3 0xfa3c6
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflictP416 : checkReasons bookP416 72 40 lastUnitsP416 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem excludeP416 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 416=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=0) h hc bp eq (by decide +kernel)
  let v := truth Z aP416
  have hbase : ValidThrough v bookP416 48 := book_start Z h hc z eq _ _ _ _ initialClausesP416
  have h0 : ValidThrough v bookP416 72 := rows_sound hbase rowsP416_0 rowsOkP416_0
  exact book_end h0 _ _ conflictP416
end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
