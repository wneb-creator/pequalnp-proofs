import CompactFramework

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.Outside.L_meta_9775.UpstreamCore.Resolution

def a177 : Array Fact := #[(.lab 0 0 2),(.lab 0 0 6),(.avoid 0 1102 0),(.res 0 6),(.res 0 8),(.res 0 10),(.res 0 11),(.lab 2 0 2),(.lab 2 1 2),(.lab 2 2 2),(.lab 3 0 3),(.lab 3 1 3),(.lab 3 2 3),(.lab 4 0 3),(.lab 4 0 6),(.avoid 4 1102 0),(.lab 6 0 6),(.lab 6 0 2),(.lab 6 0 3),(.common 6 10),(.lab 6 1 6),(.live 6 2),(.lab 6 1 2),(.lab 6 1 3),(.lab 6 2 6),(.avoid 6 541 0),(.avoid 6 541 1),(.avoid 6 541 2),(.lab 8 0 8),(.common 8 10),(.lab 8 1 8),(.live 8 2),(.lab 9 0 9),(.lab 9 1 9),(.lab 9 2 9),(.lab 10 0 10),(.live 10 1),(.lab 10 0 6),(.lab 10 0 8),(.lab 10 0 9),(.lab 10 0 11),(.common 10 11),(.lab 10 0 12),(.lab 10 0 13),(.lab 10 1 10),(.live 10 2),(.lab 10 1 6),(.lab 10 1 8),(.lab 10 1 9),(.lab 10 1 11),(.lab 10 1 12),(.lab 10 1 13),(.lab 10 2 10),(.lab 10 2 8),(.lab 10 2 9),(.lab 10 2 11),(.lab 10 2 12),(.lab 10 2 13),(.avoid 10 8488 0),(.avoid 10 8488 1),(.avoid 10 8488 2),(.avoid 10 10656 0),(.avoid 10 10656 1),(.avoid 10 10656 2),(.avoid 10 12481 0),(.avoid 10 12481 1),(.avoid 10 12481 2),(.see 10 0 1290 0),(.see 10 0 1290 1),(.see 10 0 1290 2),(.see 10 0 7426 0),(.see 10 0 7426 1),(.see 10 0 7426 2),(.see 10 0 16256 0),(.see 10 0 16256 1),(.see 10 0 16256 2),(.see 10 4 9288 0),(.see 10 4 9288 1),(.see 10 4 9288 2),(.see 10 4 9992 0),(.see 10 4 9992 1),(.see 10 4 9992 2),(.see 10 4 16256 0),(.see 10 4 16256 1),(.see 10 4 16256 2),(.see 10 5 5190 0),(.see 10 5 5190 1),(.see 10 5 5190 2),(.see 10 5 9992 0),(.see 10 5 9992 1),(.see 10 5 9992 2),(.see 10 5 13504 0),(.see 10 5 13504 1),(.see 10 5 13504 2),(.see 10 5 16256 0),(.see 10 5 16256 1),(.see 10 5 16256 2),(.diff 0 10 6),(.diff 0 10 8),(.diff 0 10 11),(.lab 11 0 8),(.lab 11 0 10),(.live 11 2),(.lab 11 1 8),(.lab 11 1 10),(.avoid 11 1290 0),(.avoid 11 1290 1),(.avoid 11 1290 2),(.reader false 0 0),(.es false 0 2),(.es false 0 6),(.reader false 5 0),(.reader false 5 1),(.reader false 5 2),(.es false 5 2),(.reader false 8 0),(.reader false 8 1),(.reader false 8 2),(.es false 8 3),(.reader false 10 0),(.reader false 11 0),(.es false 11 3),(.es false 11 6),(.reader false 13 0),(.reader false 14 0),(.reader false 16 0),(.reader false 16 1),(.reader false 16 2),(.es false 16 2),(.es false 16 6),(.reader false 18 0),(.reader false 18 1),(.reader false 18 2),(.es false 18 3),(.es false 18 6),(.reader true 0 0),(.reader true 0 1),(.reader true 0 2),(.reader true 5 0),(.reader true 5 1),(.reader true 5 2),(.reader true 8 0),(.reader true 8 1),(.reader true 8 2),(.reader true 10 0),(.reader true 10 1),(.reader true 10 2),(.es true 10 10),(.reader true 11 0),(.reader true 11 1),(.reader true 11 2),(.es true 11 10),(.reader true 13 0),(.reader true 13 1),(.reader true 13 2),(.es true 13 9),(.reader true 14 0),(.reader true 14 1),(.reader true 14 2),(.es true 14 9),(.reader true 16 0),(.reader true 16 1),(.reader true 16 2),(.es true 16 8),(.reader true 18 0),(.reader true 18 1),(.reader true 18 2),(.es true 18 8),(.gate 0 5),(.gate 0 16),(.gate 5 16),(.gate 8 11),(.gate 8 18),(.gate 10 11),(.gate 11 18),(.gate 13 14),(.gate 16 18)]
def r177 : List Scheme := [(.exposure 0 1102),(.avoidNot 0 2 1102 0),(.avoidNot 0 6 1102 0),(.self 2 0),(.self 2 1),(.self 2 2),(.self 3 0),(.self 3 1),(.self 3 2),(.exposure 4 1102),(.avoidNot 4 3 1102 0),(.avoidNot 4 6 1102 0),(.self 6 0),(.self 6 1),(.self 6 2),(.someRes 6),(.exposure 6 541),(.avoidNot 6 2 541 0),(.avoidNot 6 3 541 0),(.avoidNot 6 2 541 1),(.avoidNot 6 3 541 1),(.avoidLive 6 541 2),(.resCommon 6 10 0),(.self 8 0),(.self 8 1),(.someRes 8),(.adjacentCommon 8 10 0),(.self 9 0),(.self 9 1),(.self 9 2),(.self 10 0),(.self 10 1),(.earlier 10 1),(.self 10 2),(.exposure 10 8488),(.avoidNot 10 13 8488 0),(.avoidNot 10 13 8488 1),(.avoidNot 10 8 8488 2),(.exposure 10 10656),(.avoidNot 10 11 10656 0),(.avoidNot 10 8 10656 1),(.avoidNot 10 13 10656 1),(.avoidNot 10 8 10656 2),(.avoidNot 10 13 10656 2),(.exposure 10 12481),(.avoidNot 10 6 12481 0),(.avoidNot 10 12 12481 0),(.avoidNot 10 13 12481 0),(.avoidNot 10 6 12481 1),(.avoidNot 10 12 12481 1),(.avoidNot 10 13 12481 1),(.avoidNot 10 12 12481 2),(.avoidNot 10 13 12481 2),(.exactAt 10 0 1290),(.seeLab 10 0 8 1290 0),(.seeLab 10 0 8 1290 1),(.seeLive 10 0 1290 2),(.seeLab 10 0 8 1290 2),(.exactAt 10 0 7426),(.seeLab 10 0 8 7426 0),(.seeLab 10 0 11 7426 0),(.seeLab 10 0 8 7426 1),(.seeLab 10 0 11 7426 1),(.seeLab 10 0 8 7426 2),(.seeLab 10 0 11 7426 2),(.exactAt 10 0 16256),(.seeLab 10 0 8 16256 0),(.seeLab 10 0 11 16256 1),(.seeLab 10 0 9 16256 2),(.exactAt 10 4 9288),(.seeLab 10 4 6 9288 0),(.seeLab 10 4 13 9288 0),(.seeLab 10 4 6 9288 1),(.seeLab 10 4 13 9288 1),(.seeLab 10 4 13 9288 2),(.exactAt 10 4 9992),(.seeLab 10 4 8 9992 0),(.seeLab 10 4 9 9992 0),(.seeLive 10 4 9992 1),(.seeLab 10 4 8 9992 1),(.seeLab 10 4 9 9992 1),(.seeLab 10 4 13 9992 1),(.seeLive 10 4 9992 2),(.seeLab 10 4 8 9992 2),(.seeLab 10 4 9 9992 2),(.seeLab 10 4 13 9992 2),(.exactAt 10 4 16256),(.seeLab 10 4 12 16256 0),(.seeLab 10 4 9 16256 1),(.seeLab 10 4 13 16256 2),(.exactAt 10 5 5190),(.seeLab 10 5 12 5190 0),(.seeLab 10 5 6 5190 1),(.seeLab 10 5 12 5190 2),(.exactAt 10 5 9992),(.seeLab 10 5 8 9992 0),(.seeLab 10 5 9 9992 0),(.seeLab 10 5 8 9992 1),(.seeLab 10 5 9 9992 1),(.seeLive 10 5 9992 2),(.seeLab 10 5 8 9992 2),(.seeLab 10 5 9 9992 2),(.exactAt 10 5 13504),(.seeLab 10 5 6 13504 0),(.seeLab 10 5 12 13504 0),(.seeLab 10 5 6 13504 1),(.seeLab 10 5 12 13504 1),(.seeLab 10 5 13 13504 1),(.seeLab 10 5 12 13504 2),(.seeLab 10 5 13 13504 2),(.exactAt 10 5 16256),(.seeLab 10 5 8 16256 0),(.seeLab 10 5 9 16256 0),(.seeLab 10 5 8 16256 1),(.seeLab 10 5 9 16256 1),(.seeLab 10 5 11 16256 1),(.seeLab 10 5 8 16256 2),(.seeLab 10 5 9 16256 2),(.seeLab 10 5 11 16256 2),(.seeLab 10 5 12 16256 2),(.diffC 0 10 6),(.residual 10 6 0 1),(.diffX 0 10 8),(.diffC 0 10 8),(.residual 10 8 0 1),(.residual 10 8 0 2),(.residual 10 8 1 2),(.diffC 0 10 11),(.adjacentCommon 10 11 4),(.residual 10 11 0 1),(.residual 10 11 0 2),(.residual 10 11 1 2),(.someRes 11),(.exposure 11 1290),(.avoidNot 11 8 1290 0),(.avoidNot 11 10 1290 0),(.avoidNot 11 8 1290 1),(.avoidNot 11 10 1290 1),(.avoidLive 11 1290 2),(.readerAny false 0),(.readerLab false 0 0 2 false),(.readerLab false 0 0 6 false),(.readerAny false 5),(.readerLab false 5 0 2 true),(.readerLab false 5 1 2 true),(.readerLab false 5 2 2 true),(.readerAny false 8),(.readerLab false 8 0 3 true),(.readerLab false 8 1 3 true),(.readerLab false 8 2 3 true),(.readerAny false 10),(.readerAny false 11),(.readerLab false 11 0 3 false),(.readerLab false 11 0 6 false),(.readerAny false 13),(.readerAny false 14),(.readerAny false 16),(.readerLab false 16 0 2 false),(.readerLab false 16 0 6 true),(.readerLab false 16 1 2 false),(.readerLab false 16 1 6 true),(.readerLive false 16 2),(.readerLab false 16 2 6 true),(.readerAny false 18),(.readerLab false 18 0 3 false),(.readerLab false 18 0 6 true),(.readerLab false 18 1 3 false),(.readerLab false 18 1 6 true),(.readerLive false 18 2),(.readerLab false 18 2 6 true),(.readerAny true 0),(.readerLive true 0 2),(.readerAny true 5),(.readerLive true 5 2),(.readerAny true 8),(.readerLive true 8 2),(.readerAny true 10),(.readerLab true 10 0 10 true),(.readerLab true 10 1 10 true),(.readerLab true 10 2 10 true),(.readerAny true 11),(.readerLab true 11 0 10 false),(.readerLab true 11 1 10 false),(.readerLive true 11 2),(.readerAny true 13),(.readerLab true 13 0 9 true),(.readerLab true 13 1 9 true),(.readerLab true 13 2 9 true),(.readerAny true 14),(.readerLab true 14 0 9 false),(.readerLive true 14 1),(.readerLive true 14 2),(.readerAny true 16),(.readerLab true 16 0 8 true),(.readerLab true 16 1 8 true),(.readerLive true 16 2),(.readerAny true 18),(.readerLab true 18 0 8 false),(.readerLab true 18 1 8 false),(.readerLive true 18 2),(.eqLab false 0 5 2 false),(.gateEq true 0 5 0),(.gateEq true 0 5 1),(.eqLab false 0 16 6 false),(.gateEq true 0 16 0),(.gateEq true 0 16 1),(.eqLab false 5 16 2 true),(.gateEq true 5 16 0),(.gateEq true 5 16 1),(.eqLab false 8 11 3 true),(.gateEq true 8 11 0),(.gateEq true 8 11 1),(.eqLab false 8 18 3 true),(.gateEq true 8 18 0),(.gateEq true 8 18 1),(.gateEq false 10 11 0),(.eqLab true 10 11 10 true),(.eqLab false 11 18 6 false),(.gateEq true 11 18 0),(.gateEq true 11 18 1),(.gateEq false 13 14 0),(.eqLab true 13 14 9 true),(.gateEq false 16 18 0),(.gateEq false 16 18 1),(.eqLab true 16 18 8 true)]

def table177_0 : List Nat := [321,258,0x10102,961,0x441,0x4c1,0x541,0x5c1,0x641,0x7c1,0xd0782,0xe0782,0x841,0xa41,0xc41,0x38a82]
def table177_1 : List Nat := [0x371a8cc3,0x110c82,0x120c82,0x160d02,0x170d02,0x158d82,0x27050183,0xe41,0xf41,0x48f82,0xec1,0x1041,0x10c1,0x1141,0x11c1,0x1641]
def table177_2 : List Nat := [0x249682,0x1a41,0x793b9d43,0x2b1d02,0x331d82,0x351e02,0x7f3e9ec3,0x281e82,0x2f1f02,0x331f02,0x351f82,0x391f82,0x8541a043,0x252002,0x2a2002,0x2b2002]
def table177_3 : List Nat := [0x2e2082,0x322082,0x332082,0x382102,0x392102,0x8b44a1c3,0x26a182,0x2fa202,0x2da282,0x35a282,0x9147a343,0x26a302,0x282302,0x2fa382,0x312382,0x35a402]
def table177_4 : List Nat := [0x372402,0x974aa4c3,0x26a482,0x312502,0x362582,0x9d4da643,0x252602,0x2ba602,0x2e2682,0x33a682,0x39a702,0xa350a7c3,0x262782,0x272782,0x24a802,0x2f2802]
def table177_5 : List Nat := [0x302802,0x33a802,0x2da882,0x352882,0x362882,0x39a882,0xa953a943,0x2a2902,0x302982,0x39aa02,0xaf56aac3,0x2aaa82,0x2e2b02,0x38ab82,0xb559ac43,0x262c02]
def table177_6 : List Nat := [0x27ac02,0x2f2c82,0x30ac82,0x2dad02,0x352d02,0x36ad02,0xbb5cadc3,0x252d82,0x2aad82,0x2e2e02,0x32ae02,0x332e02,0x38ae82,0x392e82,0xc15faf43,0x262f02]
def table177_7 : List Nat := [0x27af02,0x2f2f82,0x30af82,0x312f82,0x353002,0x36b002,0x373002,0x38b002,0x33082,0x30cba4b240985,0x5b102,0x43102,0x314be4d240e85,0x314d64d2d0e85,0x314d65f2d0e85,0x63182]
def table177_8 : List Nat := [0x14c1,0x31cc651241485,0x31cde512d1485,0x31cde632d1485,0x6b302,0xd76ab4c3,0x643482,0x653482,0x673502,0x683502,0x66b582,0x3641,0xda00b603,0xdc01b603,0xe370b7c3,0xe5073783]
def table177_9 : List Nat := [0xe5083803,0xe5093883,0xeb74b9c3,0xed0a3983,0xed0b3a03,0xed0c3a83,0x3bc1,0x3c41,0xf20dbc03,0xf40ebc03,0x3dc1,0x3e41,0xff7ebec3,0x10011be83,0x103103e83,0x10016bf03]
def table177_10 : List Nat := [0x103143f03,0x15bf82,0x103183f83,0x10983c143,0x10a12c103,0x10d104103,0x10a17c183,0x10d144183,0x15c202,0x10d184203,0x11388c3c3,0x1fc482,0x1198bc543,0x1fc602,0x11f8ec6c3,0x66c782]
def table177_11 : List Nat := [0x12591c843,0x127234803,0x1272c4883,0x127344903,0x12d95ca43,0x12e65ca03,0x12e68ca83,0x66cb02,0x13599cc43,0x137204c03,0x137214c83,0x137224d03,0x13d9dce43,0x13e27ce03,0x24ce82,0x2dcf02]
def table177_12 : List Nat := [0x145a1d043,0x1471c5003,0x1471e5083,0x1fd102,0x14da5d243,0x14e64d203,0x14e67d283,0x66d302,0xe46dd403,0x1518a4383,0x1518b4403,0x1026ed483,0x153a04383,0x153a14403,0x101725503,0x155a04503]
def table177_13 : List Nat := [0x155a14583,0xf3765583,0x157944683,0x157954703,0x10b765603,0x159a44683,0x159a54703,0x15b783b83,0x12f935683,0x10c7ad703,0x15da44a03,0x15da54a83,0x15f7c3d83,0x13f9b5783,0x161823e83,0x161833f03]
def table177_14 : List Nat := [0x14fa35803,1,129,0x681,0x701,0x18a5f269204,0x18a6b269684,0x18a6b2f9684,0x18e63289204,0x18e6f289684,0x18e6f319684,0x3681,0x3701,0x72b782,0x72b802,0x72b882]
def table177_15 : List Nat := [0x76b982,0x76ba02,0x76ba82,0x3c81,0x3d01,0x81be82,0x81bf02,0x81bf82,0x86c102,0x86c182,0x86c202,0x93c802,0x93c882,0x93c902,0x9bcc02,0x9bcc82]
def table177_16 : List Nat := [0x9bcd02,0xa3d002,0xa3d082,0x725402,0x815482,0x765582,0x56c1,0x97c982,0x865702,0x57c1,0x9fcd82,0x4341,0x5701,0x3b41,0x5581,0x40c1]
def table177_17 : List Nat := [0x5481,0x3941,0x5401,0xc52d2883,0xc52d2783,0x629682,0x62a802,0x3141,705,513,0xf81,0x4481,0x4601,0x5101,0x18e7d46a884,0x18ea12f1344]
def table177_18 : List Nat := [0xc7509783,0xc7509303,0x63a842,0x639342,0x31c1,769,0x3301,0x3581,0x4781,0x4b01,0x5301,0x49c1,0x4bc1,0xa75282,0xa75202,0x5381]
def table177_19 : List Nat := [0x51c1,0x5801,0x4dc1,0x4fc1,0x904b2e8184,0x2142b804104,0x2142b804184,0x10a15c003,0xaad002,0x5541,0x4041,0x6242683,0x9b409283,0x262102,0xc85242044,0x6429203]
def table177_20 : List Nat := [0x31302,0x1241,385,0xa81,0x4281,0x5601,0x4a81,0x4a41,0x4681,0x5201,0x4741,0x52c1]

def encoded177 (i : Nat) : Nat :=
  if i < 160 then
    if i < 80 then
      if i < 32 then
        if i < 16 then
          table177_0.getD (i%16) 0
        else
          table177_1.getD (i%16) 0
      else
        if i < 48 then
          table177_2.getD (i%16) 0
        else
          if i < 64 then
            table177_3.getD (i%16) 0
          else
            table177_4.getD (i%16) 0
    else
      if i < 112 then
        if i < 96 then
          table177_5.getD (i%16) 0
        else
          table177_6.getD (i%16) 0
      else
        if i < 128 then
          table177_7.getD (i%16) 0
        else
          if i < 144 then
            table177_8.getD (i%16) 0
          else
            table177_9.getD (i%16) 0
  else
    if i < 240 then
      if i < 192 then
        if i < 176 then
          table177_10.getD (i%16) 0
        else
          table177_11.getD (i%16) 0
      else
        if i < 208 then
          table177_12.getD (i%16) 0
        else
          if i < 224 then
            table177_13.getD (i%16) 0
          else
            table177_14.getD (i%16) 0
    else
      if i < 288 then
        if i < 256 then
          table177_15.getD (i%16) 0
        else
          if i < 272 then
            table177_16.getD (i%16) 0
          else
            table177_17.getD (i%16) 0
      else
        if i < 304 then
          table177_18.getD (i%16) 0
        else
          if i < 320 then
            table177_19.getD (i%16) 0
          else
            table177_20.getD (i%16) 0
def book177 (i : Nat) : Clause := let n := encoded177 i; unpackLits 9 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClauses177 : inputsOK 1 177 a177 r177 (baseBook book177 225).toList=true := by decide +kernel

def rows177_0 : List Nat := [513,0x401,0x241401,0x241601,0x68f801,0x68fa01,0x68fc01,0x2010201,0x2010401,0x2010601,0x70a2d1802,0x7122d1a02,0xd1e01,0x112001,0x152201,0x192601,0x1d2801,0x212a01,0x71a5d3002,0x7225d3202,0x313c01,0x354001,0x394401,0x314a01]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk177_0 : checkRows book177 9 225 rows177_0=true := by decide +kernel

def rows177_1 : List Nat := [0x354e01,0x395201,0x796201,0x7d6401,0x856601,0x6d7201,0x717401,0x757601,0x5d8201,0x618401,0x3ad9001,0x3b19601,0x3cda201,0x4ba59ae02,0x419b001,0x3d1b201,0x4da69b802,0x425ba01,0xfa7cbe14603,0x42e1001,0xf278bc12403,0x4360a01,0xf77b3d53803,0x43e0801]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk177_1 : checkRows book177 9 249 rows177_1=true := by decide +kernel

def rows177_2 : List Nat := [0xef773b51c03,0x4460601,0x6f389d5cce72a14cdc07,0xc86130399ca4d26080bc08,0x5f32189cae72813c971489880bc0b,0xbe62729409e4e31c54bc08,0xdcbc35300d89a4c25c58c6521c454c20d,0x45cf401,0x45cf601,0x4643201,0x4695601,0x4695a01,0x4698601,0x138f84c3a158fc405529949d00a,0x20ba888763298cdc5e381809a4b8f1087628309c48612,0x542f12cbe4c8f984ca07,0x731e1b874751f880a8532912cde4c1ec81d00f,0x37134e64b751d0a6401c8e074351d8da423d1bc80e012,0x4ce91510072381d0d476361b8f49e2928c884e10,0xe9d23f3b190c66e2f1bcbf23391887a5027c887811,0x490fe01,0x4950801,0x4991401,0x4995e01]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk177_2 : checkRows book177 9 273 rows177_2=true := by decide +kernel

def rows177_3 : List Nat := [0x4996e01,0x4998e01,0xfd7e3ed6003,0x4ae0e01,0x5aa1568886db1a192993cb10e0a,0x5b21568866d316192993cb1120a,0xc496caa5c03,0x10280c758003,0x97cc1c002,0x1007fbf97003,0x4ca1401,0x163c460f203,0x4d381009379481550cc53e09,0x274209c0a37d4c1550cc42209,0x1369aaa14603,0x158aa67b32251c8dc419408,0xac553419ac09c44a391b88475920b,0x88ce59c02,0x199985867169ac653424920d80a,0xc4cc2c368d0944533918d409,0x1c8966e2a9dc6833261bca009,0x2682c9e4ec6004,0xda45331a48e689a0bc5c2d9f4ec940c,0x29138413f9e9309606]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk177_3 : checkRows book177 9 297 rows177_3=true := by decide +kernel

def rows177_4 : List Nat := [0x135784b5f9497c4e104cd7a09,0x39110d448372893c964d381b8e4582b15cb65a2e08e684723114b255251dcba3419cfe7636a05044a23,0x5081e01,0x9d50e6e02,0x86d11a802,0x3115cdb69d16552886439aa09,0x94d196802,0x8751da402,0x8651db402,0x945215c02,0x955258802]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk177_4 : checkRows book177 9 321 rows177_4=true := by decide +kernel

def lastUnits177 := digits 9 3 0x516974a
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflict177 : checkReasons book177 332 214 lastUnits177 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem exclude177 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 177=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=1) h hc bp eq (by decide +kernel)
  let v := truth Z a177
  have hbase : ValidThrough v book177 225 := book_start Z h hc z eq _ _ _ _ initialClauses177
  have h0 : ValidThrough v book177 249 := rows_sound hbase rows177_0 rowsOk177_0
  have h1 : ValidThrough v book177 273 := rows_sound h0 rows177_1 rowsOk177_1
  have h2 : ValidThrough v book177 297 := rows_sound h1 rows177_2 rowsOk177_2
  have h3 : ValidThrough v book177 321 := rows_sound h2 rows177_3 rowsOk177_3
  have h4 : ValidThrough v book177 332 := rows_sound h3 rows177_4 rowsOk177_4
  exact book_end h4 _ _ conflict177
end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
