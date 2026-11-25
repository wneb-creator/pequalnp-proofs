import CompactPacking

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.Outside.L_meta_9775.UpstreamCore.Resolution

def aP1216 := ([0x20021,0x20821,0xa00a1,0x200a1,0x800a1,0xa08a1,0x208a1,0x808a1,0x60a7,0x260a7,0x50a8,0x8050a8,0x200c1,0xa00c1,0x10c7,0x1805,0x21805,0x21806,0x6805,0x26805,0x26806,0xa6806,0x8805,0x28806,0xa8806,0x1825,0x21825,0x6825,0x26825,0x8825,0x28825,0x6864,0x8864,0x89a4] : List Nat).toArray.map readPackedFact
def rP1216 := ([32,0x820,160,0x8a0,0x60a5,0x1808a9,0x1820a9,0x9808a9,0x9820a9,0x50a6,0x250aa,0x850aa,0x200250aa,0x200850aa,0x10c5,0x408c9,0x428c9,0x1810,0x20801812,0x20821812,0x6810,0x806812,0x22806812,0x826812,0x22826812,0x8810,0x808812,0x2808812,0x1830,0x6830,0x8830,0x209a1813,0x1a1834,0x9a1834,0x20a21813,0x221834,0xa21834,0x22a26813,0x226834,0xa26834] : List Nat).map readPackedScheme

def tableP1216_0 : List Nat := [65,193,321,705,0x26442,0xc402,0x10402,0x18482,0x1c482,0x2e542,0xc502,0x12502,0x18582,0x1e582,0x741,0x30702]
def tableP1216_1 : List Nat := [0x34702,0x427c2,0x2300783,0x2304803,0x4e942,0x280e903,0x2b08903,0x281a983,0x2b14983,0xb41,0x2e32b03,0x3036b03,0x6acc2,0x72dc2,0x7aec2,0x2944f83]
def tableP1216_2 : List Nat := [0x3f6cc83,0x3f70d03,0x2f45003,0x4174c83,0x4178d03,0x3155083,0x4374d83,0x4378e03,0x601,0x681,0x46782,0x46802,0x56902,0x56982,0xb81,0xc01]
def tableP1216_3 : List Nat := [0x45002,0x55082,0xac1,0x1081,0x8c1,0x1001,385,769,0xa01,0xf81,0xf01,0xec1,0xc81,0xd81,0xd41,0xe41]

def encodedP1216 (i : Nat) : Nat :=
  if i < 32 then
    if i < 16 then
      tableP1216_0.getD (i%16) 0
    else
      tableP1216_1.getD (i%16) 0
  else
    if i < 48 then
      tableP1216_2.getD (i%16) 0
    else
      tableP1216_3.getD (i%16) 0
def bookP1216 (i : Nat) : Clause := let n := encodedP1216 i; unpackLits 7 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClausesP1216 : inputsOK 0 1216 aP1216 rP1216 (baseBook bookP1216 40).toList=true := by decide +kernel

def rowsP1216_0 : List Nat := [0x71e01,0x72001,0x2401,0xa601,0x12c01,0x1b001,0x50cb402,0x52cb602,0x174401,0x17ca01,0x5b62802,0x196201,0x5752202,0x1a6001,0x41221429a05,0x31221839605,0x2eaefb2804,0x69c3e02,0xeb93c9ce7ac007,0x1d3c01,0x6bdc602,0x67dcc02,0x1e3801,0x1eba01]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOkP1216_0 : checkRows bookP1216 6 40 rowsP1216_0=true := by decide +kernel

def lastUnitsP1216 := digits 6 3 0x39ffe
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflictP1216 : checkReasons bookP1216 64 33 lastUnitsP1216 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem excludeP1216 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 1216=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=0) h hc bp eq (by decide +kernel)
  let v := truth Z aP1216
  have hbase : ValidThrough v bookP1216 40 := book_start Z h hc z eq _ _ _ _ initialClausesP1216
  have h0 : ValidThrough v bookP1216 64 := rows_sound hbase rowsP1216_0 rowsOkP1216_0
  exact book_end h0 _ _ conflictP1216
end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
