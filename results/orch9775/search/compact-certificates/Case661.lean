import CompactFramework

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.Outside.L_meta_9775.UpstreamCore.Resolution

def a661 : Array Fact := #[(.res 0 8),(.res 1 8),(.res 0 10),(.res 1 10),(.res 0 13),(.res 1 13),(.lab 1 0 1),(.lab 1 1 1),(.lab 1 2 1),(.lab 1 3 1),(.lab 2 0 2),(.lab 2 0 1),(.avoid 2 314 0),(.lab 4 0 1),(.lab 4 0 2),(.avoid 4 1102 0),(.live 8 1),(.lab 8 0 10),(.common 8 10),(.lab 8 0 13),(.common 8 13),(.live 8 2),(.lab 8 1 10),(.lab 8 1 13),(.live 8 3),(.lab 8 2 10),(.lab 8 2 13),(.avoid 8 9288 0),(.avoid 8 9288 1),(.avoid 8 9288 2),(.avoid 8 9288 3),(.see 8 0 9992 0),(.see 8 0 9992 1),(.see 8 0 9992 2),(.see 8 0 9992 3),(.see 8 0 16256 0),(.see 8 0 16256 1),(.see 8 0 16256 2),(.see 8 0 16256 3),(.see 8 2 8488 0),(.see 8 2 8488 1),(.see 8 2 8488 2),(.see 8 2 8488 3),(.see 8 2 9992 0),(.see 8 2 9992 1),(.see 8 2 9992 2),(.see 8 2 9992 3),(.diff 0 8 10),(.diff 1 8 10),(.diff 0 8 13),(.diff 1 8 13),(.live 10 1),(.lab 10 0 8),(.lab 10 0 11),(.common 10 13),(.live 10 2),(.lab 10 1 8),(.lab 10 1 11),(.live 10 3),(.avoid 10 2338 0),(.avoid 10 2338 1),(.avoid 10 2338 2),(.avoid 10 2338 3),(.avoid 10 10656 0),(.avoid 10 10656 1),(.avoid 10 10656 2),(.avoid 10 10656 3),(.diff 0 10 8),(.diff 1 10 8),(.lab 11 0 11),(.lab 11 1 11),(.lab 11 2 11),(.lab 11 3 11),(.lab 13 0 13),(.live 13 1),(.lab 13 0 8),(.lab 13 0 10),(.lab 13 0 11),(.lab 13 1 13),(.live 13 2),(.lab 13 1 8),(.lab 13 1 10),(.lab 13 1 11),(.lab 13 2 13),(.live 13 3),(.lab 13 2 8),(.lab 13 2 10),(.lab 13 2 11),(.lab 13 3 13),(.lab 13 3 8),(.lab 13 3 11),(.avoid 13 1290 0),(.avoid 13 1290 1),(.avoid 13 1290 2),(.avoid 13 1290 3),(.avoid 13 2338 0),(.avoid 13 2338 1),(.avoid 13 2338 2),(.avoid 13 2338 3),(.see 13 2 8488 0),(.see 13 2 8488 1),(.see 13 2 8488 2),(.see 13 2 8488 3),(.see 13 2 9992 0),(.see 13 2 9992 1),(.see 13 2 9992 2),(.see 13 2 9992 3),(.see 13 2 10656 0),(.see 13 2 10656 1),(.see 13 2 10656 2),(.see 13 2 10656 3),(.see 13 4 9992 0),(.see 13 4 9992 1),(.see 13 4 9992 2),(.see 13 4 9992 3),(.see 13 4 10656 0),(.see 13 4 10656 1),(.see 13 4 10656 2),(.see 13 4 10656 3),(.diff 0 13 8),(.diff 1 13 8),(.diff 0 13 10),(.diff 1 13 10),(.reader false 4 0),(.reader false 4 1),(.reader false 4 2),(.reader false 4 3),(.es false 4 1),(.reader false 5 0),(.reader false 6 0),(.es false 6 1),(.es false 6 2),(.reader false 10 0),(.reader false 11 0),(.reader false 12 0),(.es false 12 1),(.es false 12 2),(.reader true 4 0),(.reader true 4 1),(.reader true 4 2),(.reader true 4 3),(.reader true 5 0),(.reader true 5 1),(.reader true 5 2),(.reader true 5 3),(.es true 5 13),(.reader true 6 0),(.reader true 6 1),(.reader true 6 2),(.reader true 6 3),(.es true 6 13),(.reader true 10 0),(.reader true 10 1),(.reader true 10 2),(.reader true 10 3),(.es true 10 8),(.es true 10 11),(.reader true 11 0),(.reader true 11 1),(.reader true 11 2),(.reader true 11 3),(.es true 11 11),(.reader true 12 0),(.reader true 12 1),(.reader true 12 2),(.reader true 12 3),(.es true 12 8),(.es true 12 11),(.gate 4 6),(.gate 4 12),(.gate 5 6),(.gate 6 12),(.gate 10 11),(.gate 10 12),(.gate 11 12)]
def r661 : List Scheme := [(.self 1 0),(.self 1 1),(.self 1 2),(.self 1 3),(.self 2 0),(.exposure 2 314),(.avoidNot 2 1 314 0),(.exposure 4 1102),(.avoidNot 4 1 1102 0),(.avoidNot 4 2 1102 0),(.earlier 8 1),(.allRes 8 0),(.allRes 8 1),(.exposure 8 9288),(.avoidNot 8 10 9288 0),(.avoidNot 8 13 9288 0),(.avoidLive 8 9288 1),(.avoidNot 8 10 9288 1),(.avoidNot 8 13 9288 1),(.avoidLive 8 9288 2),(.avoidNot 8 10 9288 2),(.avoidNot 8 13 9288 2),(.avoidLive 8 9288 3),(.exactAt 8 0 9992),(.seeLab 8 0 10 9992 0),(.seeLab 8 0 13 9992 0),(.seeLab 8 0 10 9992 1),(.seeLab 8 0 13 9992 1),(.seeLive 8 0 9992 2),(.seeLab 8 0 13 9992 2),(.seeLive 8 0 9992 3),(.exactAt 8 0 16256),(.seeLab 8 0 13 16256 0),(.seeLab 8 0 13 16256 1),(.seeLab 8 0 10 16256 2),(.seeLive 8 0 16256 3),(.exactAt 8 2 8488),(.seeLab 8 2 13 8488 0),(.seeLab 8 2 13 8488 1),(.seeLive 8 2 8488 2),(.seeLive 8 2 8488 3),(.exactAt 8 2 9992),(.seeLab 8 2 10 9992 0),(.seeLab 8 2 13 9992 0),(.seeLab 8 2 10 9992 1),(.seeLab 8 2 13 9992 1),(.seeLab 8 2 10 9992 2),(.seeLab 8 2 13 9992 2),(.seeLive 8 2 9992 3),(.diffX 0 8 10),(.diffC 0 8 10),(.diffX 1 8 10),(.diffC 1 8 10),(.adjacentCommon 8 10 0),(.residual 8 10 0 1),(.residual 8 10 0 2),(.residual 8 10 1 2),(.diffC 0 8 13),(.diffX 1 8 13),(.diffC 1 8 13),(.adjacentCommon 8 13 2),(.residual 8 13 0 1),(.residual 8 13 0 2),(.residual 8 13 1 2),(.someRes 10),(.allRes 10 0),(.exposure 10 2338),(.avoidNot 10 11 2338 0),(.avoidNot 10 8 2338 1),(.avoidLive 10 2338 2),(.avoidLive 10 2338 3),(.exposure 10 10656),(.avoidNot 10 8 10656 0),(.avoidNot 10 11 10656 0),(.avoidLive 10 10656 1),(.avoidNot 10 11 10656 1),(.avoidLive 10 10656 2),(.avoidLive 10 10656 3),(.diffX 0 10 8),(.diffX 1 10 8),(.diffC 1 10 8),(.residual 10 8 0 1),(.adjacentCommon 10 13 4),(.self 11 0),(.self 11 1),(.self 11 2),(.self 11 3),(.self 13 0),(.self 13 1),(.earlier 13 1),(.self 13 2),(.earlier 13 2),(.self 13 3),(.allRes 13 0),(.allRes 13 1),(.exposure 13 1290),(.avoidNot 13 8 1290 0),(.avoidNot 13 10 1290 0),(.avoidNot 13 8 1290 1),(.avoidNot 13 10 1290 1),(.avoidNot 13 8 1290 2),(.avoidNot 13 10 1290 2),(.avoidLive 13 1290 3),(.avoidNot 13 8 1290 3),(.exposure 13 2338),(.avoidNot 13 8 2338 0),(.avoidNot 13 8 2338 1),(.avoidNot 13 8 2338 2),(.avoidNot 13 11 2338 3),(.exactAt 13 2 8488),(.seeLab 13 2 8 8488 0),(.seeLab 13 2 8 8488 1),(.seeLab 13 2 8 8488 2),(.seeLive 13 2 8488 3),(.exactAt 13 2 9992),(.seeLab 13 2 8 9992 0),(.seeLab 13 2 10 9992 0),(.seeLab 13 2 8 9992 1),(.seeLab 13 2 10 9992 1),(.seeLab 13 2 8 9992 2),(.seeLab 13 2 10 9992 2),(.seeLive 13 2 9992 3),(.exactAt 13 2 10656),(.seeLab 13 2 8 10656 0),(.seeLab 13 2 11 10656 0),(.seeLab 13 2 8 10656 1),(.seeLab 13 2 11 10656 1),(.seeLab 13 2 8 10656 2),(.seeLab 13 2 11 10656 2),(.seeLive 13 2 10656 3),(.exactAt 13 4 9992),(.seeLab 13 4 8 9992 0),(.seeLab 13 4 10 9992 0),(.seeLab 13 4 8 9992 1),(.seeLab 13 4 10 9992 1),(.seeLab 13 4 8 9992 2),(.seeLab 13 4 10 9992 2),(.seeLive 13 4 9992 3),(.seeLab 13 4 8 9992 3),(.exactAt 13 4 10656),(.seeLab 13 4 8 10656 0),(.seeLab 13 4 8 10656 1),(.seeLab 13 4 8 10656 2),(.seeLab 13 4 11 10656 3),(.diffX 0 13 8),(.diffC 0 13 8),(.diffC 1 13 8),(.residual 13 8 0 1),(.residual 13 8 0 2),(.residual 13 8 0 3),(.residual 13 8 1 2),(.residual 13 8 1 3),(.residual 13 8 2 3),(.diffX 0 13 10),(.diffC 0 13 10),(.diffX 1 13 10),(.diffC 1 13 10),(.residual 13 10 0 1),(.residual 13 10 0 2),(.residual 13 10 1 2),(.readerAny false 4),(.readerLab false 4 0 1 true),(.readerLab false 4 1 1 true),(.readerLab false 4 2 1 true),(.readerLab false 4 3 1 true),(.readerAny false 5),(.readerAny false 6),(.readerLab false 6 0 1 false),(.readerLab false 6 0 2 true),(.readerAny false 10),(.readerAny false 11),(.readerAny false 12),(.readerLab false 12 0 1 false),(.readerLab false 12 0 2 false),(.readerAny true 4),(.readerLive true 4 2),(.readerLive true 4 3),(.readerAny true 5),(.readerLab true 5 0 13 false),(.readerLab true 5 1 13 false),(.readerLive true 5 2),(.readerLab true 5 2 13 false),(.readerLive true 5 3),(.readerAny true 6),(.readerLab true 6 0 13 true),(.readerLab true 6 1 13 true),(.readerLive true 6 2),(.readerLab true 6 2 13 true),(.readerLive true 6 3),(.readerLab true 6 3 13 true),(.readerAny true 10),(.readerLab true 10 0 8 true),(.readerLab true 10 0 11 false),(.readerLive true 10 1),(.readerLab true 10 1 8 true),(.readerLab true 10 1 11 false),(.readerLive true 10 2),(.readerLive true 10 3),(.readerAny true 11),(.readerLab true 11 0 11 true),(.readerLab true 11 1 11 true),(.readerLab true 11 2 11 true),(.readerLab true 11 3 11 true),(.readerAny true 12),(.readerLab true 12 0 8 false),(.readerLab true 12 0 11 false),(.readerLab true 12 1 8 false),(.readerLab true 12 1 11 false),(.readerLive true 12 2),(.readerLab true 12 2 8 false),(.readerLab true 12 2 11 false),(.readerLive true 12 3),(.eqLab false 4 6 1 true),(.gateEq true 4 6 0),(.gateEq true 4 6 1),(.eqLab false 4 12 1 true),(.gateEq true 4 12 0),(.gateEq true 4 12 1),(.gateEq false 5 6 0),(.eqLab true 5 6 13 false),(.eqLab false 6 12 2 true),(.gateEq true 6 12 0),(.gateEq true 6 12 1),(.gateEq false 10 11 0),(.eqLab true 10 11 11 false),(.gateEq false 10 12 0),(.eqLab true 10 12 8 true),(.gateEq false 11 12 0),(.eqLab true 11 12 11 true)]

def table661_0 : List Nat := [833,961,0x441,0x4c1,0x541,0x641,0xb0602,0x7c1,0xd0782,0xe0782,0x108a82,0x8c02,0x18c02,0x7a3b1c8dc4,0x110d82,0x130d82]
def table661_1 : List Nat := [0x108e02,0x160e02,0x170e02,0x158e82,0x190e82,0x1a0e82,0x188f02,0x8a43208fc4,0x118f82,0x130f82,0x169002,0x171002,0x159082,0x1a1082,0x189102,0x9a4b2491c4]
def table661_2 : List Nat := [0x131182,0x171202,0x199282,0x189302,0xaa532893c4,0x139382,0x179402,0x159482,0x189502,0xba5b2c95c4,0x111582,0x139582,0x161602,0x179602,0x191682,0x1a9682]
def table661_3 : List Nat := [0x189702,0x9782,0x21782,0x19802,0x31802,0x941,0x3097c5a23100906,0x3097c6623150906,0x3097c662d150906,0x41882,0x19902,0x51902,0xa41,0x3298c5e27100a06,0x3298c6a27150a06,0x3298c6a2f150a06]
def table661_4 : List Nat := [0x7029b83,0x29d02,0xfa7b3c9dc4,0x351d82,0x381e02,0x379e82,0x3a9f02,0x10a83409fc4,0x341f82,0x351f82,0x33a002,0x392002,0x37a082,0x3aa102,0x2a182,0x3a202]
def table661_5 : List Nat := [0x12202,0x44a1ce269330906,0x1b41,0x22c1,0x2341,0x23c1,0x2441,0x24c1,0x2741,0x4aa782,0x29c1,0x4faa02,0x2c41,0x4aa02,0x5aa02,0x17abb5cadc4]
def table661_6 : List Nat := [0x4b2d82,0x4c2d82,0x502e02,0x512e02,0x552e82,0x562e82,0x54af02,0x592f02,0x18ac360afc4,0x4b2f82,0x503002,0x553082,0x5a3102,0x19acb64b1c4,0x4bb182,0x50b202]
def table661_7 : List Nat := [0x55b282,0x54b302,0x1aad368b3c4,0x4bb382,0x4c3382,0x50b402,0x513402,0x55b482,0x563482,0x54b502,0x1badb6cb5c4,0x4bb582,0x4d3582,0x50b602,0x523602,0x55b682]
def table661_8 : List Nat := [0x573682,0x54b702,0x1cae370b7c4,0x4b3782,0x4cb782,0x503802,0x51b802,0x553882,0x56b882,0x54b902,0x593902,0x1daeb74b9c4,0x4b3982,0x503a02,0x553a82,0x5abb02]
def table661_9 : List Nat := [0x4bb82,0x3b82,0x13c02,0x78bbd42974a0a06,0x78bbd56974f0a06,0x78bbd6697540a06,0x78bbd56a14f0a06,0x78bbd66a1540a06,0x78bbd66ab540a06,0x4bc82,0x23c82,0x5bd02,0x33d02,0x7abcd46994a1b06,0x7abcd5a994f1b06,0x7abcd5aa34f1b06]
def table661_10 : List Nat := [0x1fafb7cbdc4,0xff063d83,0xff073e03,0xff083e83,0xff093f03,0x4041,0x40c1,0x1040bc083,0x1070a4083,0x4241,0x42c1,0x4341,0x10e0dc303,0x1100ec303,0x233178ac4c4,0x4fc582]
def table661_11 : List Nat := [0x54c602,0x2431f8ec6c4,0x12213c683,0x12217c703,0x15c782,0x1221ac783,0x18c802,0x2572993c944,0x12d494903,0x12d4e4983,0x4fca02,0x12d534a03,0x54ca82,0x12d584a83,0x26b3398cbc4,0x137344b83]
def table661_12 : List Nat := [0x13835cb83,0x33cc02,0x137384c03,0x13839cc03,0x37cc82,0x3acd02,0x2833f9ecec4,0x143454e83,0x143464f03,0x143474f83,0x143485003,0x29749a3d144,0x14c4bd103,0x14e4dd103,0x14c50d183,0x14e52d183]
def table661_13 : List Nat := [0x4fd202,0x14c55d203,0x14e57d203,0x54d282,0x1057f5403,0x151924483,0x151934503,0x10f7f5483,0x153a24483,0x153a34503,0x155814003,0x12c91d503,0x111835583,0x157a24903,0x157a34983,0x159854203]
def table661_14 : List Nat := [0x1429cd603,0x15b864203,0x14d9b5683,0x15d864283,0x14fa15703,0x581,0x681,0x701,0x184be2d118805,0x184be33118a85,0x184be33168a85,0x194c62f138805,0x194c635138a85,0x194c635178a85,0x2250e71349985,0x3c5dea14ba505]
def table661_15 : List Nat := [0x3c5deab4ba785,0x3c5deb34baa05,0x3c5deab50a785,0x3c5deb350aa05,0x3c5deb355aa05,0x3d5e6a34ca505,0x3d5e6ad4ca785,0x3d5e6ad51a785,0x7fbd82,0x7fbe02,0x7fbe82,0x7fbf02,0x4101,0x41c1,0x4381,0x4401]
def table661_16 : List Nat := [0x96c902,0x96c982,0x96ca02,0x96ca82,0xa1ce82,0xa1cf02,0xa1cf82,0xa1d002,0x7f5402,0x7f5482,0x5541,0x9648c2,0x5581,0xa24902,0xa34982,0x5641]
def table661_17 : List Nat := [0xa14e42,0x56c1,0xa6cd82,0x5741,0xa7d082,0x3fc1,0x5401,0x5481,0xaa502583,0xaa502c83,0x311a0b83,0x1512218c784,0x15122189004,0xa8268e83,0x2a08a411a8d85,0x540f48a411d8d46]
def table661_18 : List Nat := [0xa8910c43,0x15097598c04,0x4b41,0x48c1,0xa8552803,0x542a82,0x2a01,0x2f01,0x3301,0x3501,0x3701,0x3901,0x4601,0x4a81,0x5281,0x502582]
def table661_19 : List Nat := [0x29d4c55a5c4,0x14ea62ac3,0x552582,0x14ea62843,0xa75302,0x502a82,0x9ba240a839c4c06,0x4dd120537ce05,0x50c1,0x4e41,0x184023b1789c5,0xc2011d8d04,0xc2012d8e04,0x61008ec3,0x308042,0x29cf177a804]
def table661_20 : List Nat := [0x29cf177aac4,0x4fd182,0x27c1,0x2541,0x14e78bbc3,0x26e89038144,0x1e6b74cbd44,0xee328e83,0x1dc651a8a84,0x623b218b84,0x311d8ac3,0x771942,0xf37aa583,0xf37aa803,0x79bd42,0xa70082]
def table661_21 : List Nat := [0xcbe2a2c8b45,0x65f1d9644,0x32f8ec3,0x197c2,0xa701c2,0xa70e82,0xa70d42,0x5381]

def encoded661 (i : Nat) : Nat :=
  if i < 176 then
    if i < 80 then
      if i < 32 then
        if i < 16 then
          table661_0.getD (i%16) 0
        else
          table661_1.getD (i%16) 0
      else
        if i < 48 then
          table661_2.getD (i%16) 0
        else
          if i < 64 then
            table661_3.getD (i%16) 0
          else
            table661_4.getD (i%16) 0
    else
      if i < 128 then
        if i < 96 then
          table661_5.getD (i%16) 0
        else
          if i < 112 then
            table661_6.getD (i%16) 0
          else
            table661_7.getD (i%16) 0
      else
        if i < 144 then
          table661_8.getD (i%16) 0
        else
          if i < 160 then
            table661_9.getD (i%16) 0
          else
            table661_10.getD (i%16) 0
  else
    if i < 256 then
      if i < 208 then
        if i < 192 then
          table661_11.getD (i%16) 0
        else
          table661_12.getD (i%16) 0
      else
        if i < 224 then
          table661_13.getD (i%16) 0
        else
          if i < 240 then
            table661_14.getD (i%16) 0
          else
            table661_15.getD (i%16) 0
    else
      if i < 304 then
        if i < 272 then
          table661_16.getD (i%16) 0
        else
          if i < 288 then
            table661_17.getD (i%16) 0
          else
            table661_18.getD (i%16) 0
      else
        if i < 320 then
          table661_19.getD (i%16) 0
        else
          if i < 336 then
            table661_20.getD (i%16) 0
          else
            table661_21.getD (i%16) 0
def book661 (i : Nat) : Clause := let n := encoded661 i; unpackLits 9 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClauses661 : inputsOK 2 661 a661 r661 (baseBook book661 229).toList=true := by decide +kernel

def rows661_0 : List Nat := [0x140c01,0x1c1001,0x1c1201,0xd46c01,0xd46e01,0xd47001,0xf07a01,0xf07c01,0xf07e01,0xd4a201,0xf12601,0xf12801,0xf12a01,0xf12c01,0xf12e01,0xf13001,0x1493a01,0x1493c01,0x1493e01,0x14201,0x54401,0x94601,0xd4801,0x72a994e02]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk661_0 : checkRows book661 9 229 rows661_0=true := by decide +kernel

def rows661_1 : List Nat := [0x22995002,0x732ad5802,0x73aad5a02,0x15d7001,0x1617201,0x1697601,0x1717a01,0x14d8e01,0x1519001,0x1559201,0x1599401,0x3f1a801,0x3f9ae01,0x53295b402,0x429b601,0x7fbf5b802,0x431ba01,0x431bc01,0x552a5be02,0x43dc001,0x55aa5c202,0x445c401,0x55aa9c602,0x44dc801]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk661_1 : checkRows book661 9 253 rows661_1=true := by decide +kernel

def rows661_2 : List Nat := [0x1f6fa7cbe14004,0x4561001,0x4561201,0x1b11668461a4d68e352351e09,0x185045f4519cc887312150809,0x382e0d0d8482c1e0a8743009,0x885c1a1907bae341d0a8296ab41c974765e0b0783412,0x54260d07ac962b30886c34392e8ecbc165b46dda11,0x3e2076889d8150a04c725d1d978420c,0x5dd81807838725d1d9783809,0x381976bac241006c78725d1d9782e0c,0x5886566178d0763f1d8e46d6c230f059640e,0x124910602de204,0x2070280c016e04,0x48a1601,0x233189048e4204,0xc6822fa0cc08a33bbde72443990b25b4882d240c9048d0c14,0xca822fa0cc08531228cef0793d24a924883017202dc8d1014,0x498cc01,0x498e201,0x498f201,0x4990201,0x4991201,0x4996001]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk661_2 : checkRows book661 9 277 rows661_2=true := by decide +kernel

def rows661_3 : List Nat := [0x4997801,0x499a601,0x195045f41980c48595c9d1009,0x1f9967a661ecfed1974a99e09,0x7c659e99c7d97cc1a27f974a99a0b,0x18d045f41980c88795c9d0c09,0x80659e99c7d3db326531974a9a40b,0x614117d0a6299a1cc93193cad080b,0x185045f43990c48595c9d0809,0x12096ee61b09824e269048e09,0x251108e422490d80bf5f4d89c4626b14824526311dc12,0x20f0682c118c04,0x4e22001,0x441cea748b84e29120ac4a310b0a0600b130b41a11,0x110b834320f9d4683a160f02c340b,0xa85ae80904420311802c5209,0x38e80b8b036299d0ac300f07036782f9d8c42c1e1802c1414,0x542c17ba5d4150a04e7a301882c520c,0x5baba1ad865b4174af7833cfc7a3f9ee6b2f8b4b65917974a9ac16,0x2dd5d0e6cb2d9a7c682e95e7a791fcfb3f8b4b65917974a9aa15,0x5baba1cd957aea2d2d9645daa0a,0x5baba1ad865d05a0ba57c5a5b2c8bcb9ac0e,0x508b201,0x1df409fd0e6404]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk661_3 : checkRows book661 9 301 rows661_3=true := by decide +kernel

def rows661_4 : List Nat := [0x9bce48002,0x6332bd5ed27a1d08be07,0x8042ec768882a14098e5202305a443e0d,0x7849d8ed1ca402c0b48d1c1a0a,0xe0b83436120b0783007,0x885c1a19078944826a489c38160f0a0340e,0x885c1a1907bae341da402a95471ca402c1e05a443412,0xe8773ad1a652f304a4e408,0x6530bddea76391de6a6239d324f42a1ca4be0f,0x6330bddec643c1c0e46d3a9be9a73375325129a149cbe13,0x26c774b4d514693e48d112450894d29c0d,0x5c2a753a06630060285208,0xb856e9078381a11a80cc2c30a5030520d,0xe093a05a2ca882a94330b0301a0b,0x542c17ba5d4150a04ea43318030520c,0x27c4a6832a9d3e8a06,0x8042ec768882a14098e8460ca78e5334e4e5503e11,0xf093b1da3a0b0e5334e4e55295550653c1a0f,0x885c1a1907bae341dab02a95551ca669c9caa0782c3a0653c3416]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk661_4 : checkRows book661 9 325 rows661_4=true := by decide +kernel

def lastUnits661 := digits 9 2 0x2af38
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflict661 : checkReasons book661 344 276 lastUnits661 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem exclude661 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 661=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=2) h hc bp eq (by decide +kernel)
  let v := truth Z a661
  have hbase : ValidThrough v book661 229 := book_start Z h hc z eq _ _ _ _ initialClauses661
  have h0 : ValidThrough v book661 253 := rows_sound hbase rows661_0 rowsOk661_0
  have h1 : ValidThrough v book661 277 := rows_sound h0 rows661_1 rowsOk661_1
  have h2 : ValidThrough v book661 301 := rows_sound h1 rows661_2 rowsOk661_2
  have h3 : ValidThrough v book661 325 := rows_sound h2 rows661_3 rowsOk661_3
  have h4 : ValidThrough v book661 344 := rows_sound h3 rows661_4 rowsOk661_4
  exact book_end h4 _ _ conflict661
end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
