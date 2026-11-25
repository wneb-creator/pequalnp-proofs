import CompactFramework

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.Outside.L_meta_9775.UpstreamCore.Resolution

def a11 : Array Fact := #[(.lab 8 0 9),(.lab 8 0 10),(.lab 8 0 11),(.lab 8 1 9),(.lab 8 1 10),(.lab 8 1 11),(.avoid 8 1548 0),(.avoid 8 1548 1),(.avoid 8 7174 0),(.avoid 8 7174 1),(.see 8 0 7426 0),(.see 8 0 7426 1),(.see 8 0 9992 0),(.see 8 0 9992 1),(.lab 9 0 9),(.lab 9 1 9),(.lab 11 0 11),(.lab 11 0 9),(.lab 11 0 12),(.lab 11 1 11),(.lab 11 1 9),(.lab 11 1 12),(.avoid 11 4757 0),(.avoid 11 4757 1),(.see 11 3 6789 0),(.see 11 3 6789 1),(.reader false 16 0),(.reader false 16 1),(.reader false 17 0),(.reader false 17 1),(.reader false 18 0),(.reader false 18 1),(.reader true 16 0),(.reader true 16 1),(.es true 16 9),(.es true 16 11),(.reader true 17 0),(.reader true 17 1),(.es true 17 9),(.reader true 18 0),(.reader true 18 1),(.es true 18 9),(.es true 18 11),(.gate 16 17),(.gate 16 18),(.gate 17 18)]
def r11 : List Scheme := [(.exposure 8 1548),(.avoidNot 8 9 1548 0),(.avoidNot 8 10 1548 0),(.avoidNot 8 9 1548 1),(.avoidNot 8 10 1548 1),(.exposure 8 7174),(.avoidNot 8 10 7174 0),(.avoidNot 8 11 7174 0),(.avoidNot 8 10 7174 1),(.avoidNot 8 11 7174 1),(.exactAt 8 0 7426),(.seeLab 8 0 10 7426 0),(.seeLab 8 0 11 7426 0),(.seeLab 8 0 10 7426 1),(.seeLab 8 0 11 7426 1),(.exactAt 8 0 9992),(.seeLab 8 0 9 9992 0),(.seeLab 8 0 10 9992 0),(.seeLab 8 0 9 9992 1),(.seeLab 8 0 10 9992 1),(.self 9 0),(.self 9 1),(.self 11 0),(.self 11 1),(.exposure 11 4757),(.avoidNot 11 9 4757 0),(.avoidNot 11 12 4757 0),(.avoidNot 11 9 4757 1),(.avoidNot 11 12 4757 1),(.exactAt 11 3 6789),(.seeLab 11 3 9 6789 0),(.seeLab 11 3 12 6789 0),(.seeLab 11 3 9 6789 1),(.seeLab 11 3 12 6789 1),(.readerAny false 16),(.readerAny false 17),(.readerAny false 18),(.readerAny true 16),(.readerLab true 16 0 9 false),(.readerLab true 16 0 11 false),(.readerLab true 16 1 9 false),(.readerLab true 16 1 11 false),(.readerAny true 17),(.readerLab true 17 0 9 true),(.readerLab true 17 1 9 true),(.readerAny true 18),(.readerLab true 18 0 9 false),(.readerLab true 18 0 11 true),(.readerLab true 18 1 9 false),(.readerLab true 18 1 11 true),(.gateEq false 16 17 0),(.gateEq false 16 17 1),(.eqLab true 16 17 9 false),(.gateEq false 16 18 0),(.gateEq false 16 18 1),(.eqLab true 16 18 11 false),(.gateEq false 17 18 0),(.gateEq false 17 18 1),(.eqLab true 17 18 9 true)]

def table11_0 : List Nat := [0x1e342,770,0x4302,0xc382,0x10382,0x26442,0x4402,0x8402,0x10482,0x14482,0x2e542,0x6502,0x8502,0x12582,0x14582,0x36642]
def table11_1 : List Nat := [0x602,0x6602,0xc682,0x12682,0x741,0x7c1,0x841,0x9c1,0x5eb42,0x44b02,0x48b02,0x50b82,0x54b82,0x66c42,0x44c02,0x4ac02]
def table11_2 : List Nat := [0x50c82,0x56c82,0x6ed42,0x76e42,0x7ef42,0x87042,0x4403003,0x460b003,0x440f083,0x4617083,0x97242,0x4d39203,0x4d3d283,0xa33c2,0x5247383,0x5541383]
def table11_3 : List Nat := [0x5253403,0x554d403,0x5770d03,0x5774d83,0x4c8b583,0x5978d03,0x597cd83,0x548f603,0x5b78e03,0x5b7ce83,0x5399683,0x9b202,0x9b282,0xab382,0xab402,0xa01]
def table11_4 : List Nat := [0x881,0x1481,0x1341,0x1681,385,1,0x1101,0x1581,257,641,0x1181,0x1541,0x1601,0xf81,0xf41,0xd01]
def table11_5 : List Nat := [0xe01,0xdc1,0xec1]

def encoded11 (i : Nat) : Nat :=
  if i < 48 then
    if i < 16 then
      table11_0.getD (i%16) 0
    else
      if i < 32 then
        table11_1.getD (i%16) 0
      else
        table11_2.getD (i%16) 0
  else
    if i < 64 then
      table11_3.getD (i%16) 0
    else
      if i < 80 then
        table11_4.getD (i%16) 0
      else
        table11_5.getD (i%16) 0
def book11 (i : Nat) : Clause := let n := encoded11 i; unpackLits 7 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClauses11 : inputsOK 0 11 a11 r11 (baseBook book11 59).toList=true := by decide +kernel

def rows11_0 : List Nat := [0x145601,0x155801,0x165e01,0x176201,0x1a3a6101b3e05,0x1c3a60f194205,0x5cc203f5a04,0x1e3b5402,0x20c27402,0x21e009032205,0x41e008012605,0x4ca22c44a04,0x21466802,0x814146071a05,0x614147091605,0x529e4c84a04,0x1f3d5a02,0x254b6e02,0x8d1396d1e1cc6407,0x4d4801,0x264e6a02,0x21ce7002,0x4f4401,0x504601]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk11_0 : checkRows book11 7 59 rows11_0=true := by decide +kernel

def lastUnits11 := digits 7 3 0x11e8d2
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflict11 : checkReasons book11 83 51 lastUnits11 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem exclude11 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 11=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=0) h hc bp eq (by decide +kernel)
  let v := truth Z a11
  have hbase : ValidThrough v book11 59 := book_start Z h hc z eq _ _ _ _ initialClauses11
  have h0 : ValidThrough v book11 83 := rows_sound hbase rows11_0 rowsOk11_0
  exact book_end h0 _ _ conflict11
end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
