import CompactFramework

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.Outside.L_meta_9775.UpstreamCore.Resolution

def a1290 : Array Fact := #[(.res 0 5),(.res 0 6),(.res 0 9),(.res 0 13),(.lab 1 0 5),(.avoid 1 245 0),(.lab 5 0 5),(.common 5 6),(.lab 5 1 5),(.live 5 2),(.lab 5 2 5),(.live 6 1),(.lab 6 0 0),(.lab 6 0 5),(.common 6 9),(.lab 6 0 13),(.common 6 13),(.live 6 2),(.lab 6 1 0),(.lab 6 1 5),(.lab 6 1 13),(.lab 6 2 0),(.lab 6 2 5),(.lab 6 2 13),(.avoid 6 2087 0),(.avoid 6 2087 1),(.avoid 6 2087 2),(.avoid 6 10401 0),(.avoid 6 10401 1),(.avoid 6 10401 2),(.avoid 6 14977 0),(.avoid 6 14977 1),(.avoid 6 14977 2),(.see 6 8 127 0),(.see 6 8 127 1),(.see 6 8 127 2),(.see 6 8 8297 0),(.see 6 8 8297 1),(.see 6 8 8297 2),(.see 6 8 12481 0),(.see 6 8 12481 1),(.see 6 8 12481 2),(.diff 0 6 5),(.diff 0 6 13),(.lab 7 0 7),(.lab 7 1 7),(.lab 7 2 7),(.lab 8 0 9),(.lab 8 0 11),(.avoid 8 541 0),(.avoid 8 2087 0),(.lab 9 0 9),(.live 9 1),(.live 9 0),(.lab 9 0 6),(.lab 9 0 7),(.lab 9 0 11),(.common 9 11),(.lab 9 0 12),(.lab 9 1 9),(.live 9 2),(.lab 9 1 6),(.lab 9 1 7),(.lab 9 1 11),(.lab 9 1 12),(.lab 9 2 9),(.lab 9 2 6),(.lab 9 2 7),(.lab 9 2 11),(.avoid 9 245 0),(.avoid 9 245 1),(.avoid 9 245 2),(.avoid 9 2213 0),(.avoid 9 2213 1),(.avoid 9 2213 2),(.avoid 9 4309 0),(.avoid 9 4309 1),(.avoid 9 4309 2),(.see 9 1 6789 0),(.see 9 1 6789 1),(.see 9 1 6789 2),(.diff 0 9 6),(.lab 10 0 9),(.lab 10 0 12),(.avoid 10 541 0),(.avoid 10 4183 0),(.lab 11 0 11),(.live 11 1),(.lab 11 0 7),(.lab 11 0 9),(.lab 11 1 11),(.live 11 2),(.lab 11 1 7),(.lab 11 1 9),(.lab 11 2 11),(.lab 11 2 7),(.lab 11 2 9),(.avoid 11 5008 0),(.avoid 11 5008 1),(.avoid 11 5008 2),(.avoid 11 13504 0),(.avoid 11 13504 1),(.avoid 11 13504 2),(.see 11 3 6789 0),(.see 11 3 6789 1),(.see 11 3 6789 2),(.diff 0 11 9),(.lab 12 0 12),(.lab 12 1 12),(.lab 12 2 12),(.lab 13 0 6),(.lab 13 0 7),(.live 13 2),(.lab 13 1 6),(.lab 13 1 7),(.avoid 13 245 0),(.avoid 13 245 1),(.avoid 13 245 2),(.see 13 1 8417 0),(.see 13 1 8417 1),(.see 13 1 8417 2),(.reader false 2 0),(.reader false 3 0),(.es false 3 5),(.reader false 4 0),(.reader false 7 0),(.reader false 8 0),(.reader false 13 0),(.reader false 13 1),(.reader false 13 2),(.es false 13 5),(.reader false 14 0),(.reader false 14 1),(.reader false 14 2),(.reader false 15 0),(.reader false 15 1),(.reader false 15 2),(.reader false 16 0),(.reader false 16 1),(.reader false 16 2),(.reader false 17 0),(.reader false 17 1),(.reader false 17 2),(.reader false 18 0),(.reader false 18 1),(.reader false 18 2),(.reader true 2 0),(.reader true 2 1),(.reader true 2 2),(.es true 2 7),(.reader true 3 0),(.reader true 3 1),(.reader true 3 2),(.es true 3 6),(.es true 3 7),(.reader true 4 0),(.reader true 4 1),(.reader true 4 2),(.es true 4 6),(.es true 4 7),(.reader true 7 0),(.reader true 7 1),(.reader true 7 2),(.es true 7 7),(.reader true 8 0),(.reader true 8 1),(.reader true 8 2),(.es true 8 7),(.reader true 13 0),(.reader true 13 1),(.reader true 13 2),(.es true 13 9),(.es true 13 12),(.reader true 14 0),(.es true 14 9),(.es true 14 12),(.reader true 15 0),(.reader true 15 1),(.reader true 15 2),(.es true 15 12),(.reader true 16 0),(.es true 16 9),(.es true 16 11),(.reader true 17 0),(.reader true 17 1),(.reader true 17 2),(.es true 17 9),(.es true 17 11),(.reader true 18 0),(.reader true 18 1),(.reader true 18 2),(.es true 18 11),(.gate 2 3),(.gate 2 4),(.gate 3 4),(.gate 3 13),(.gate 7 8),(.gate 13 14),(.gate 13 15),(.gate 14 15),(.gate 16 17),(.gate 16 18),(.gate 17 18)]
def r1290 : List Scheme := [(.exposure 1 245),(.avoidNot 1 5 245 0),(.self 5 0),(.self 5 1),(.self 5 2),(.someRes 5),(.resCommon 5 6 0),(.earlier 6 1),(.someRes 6),(.exposure 6 2087),(.avoidNot 6 0 2087 0),(.avoidNot 6 5 2087 0),(.avoidNot 6 5 2087 1),(.avoidNot 6 0 2087 2),(.avoidNot 6 5 2087 2),(.exposure 6 10401),(.avoidNot 6 5 10401 0),(.avoidNot 6 0 10401 1),(.avoidNot 6 5 10401 2),(.exposure 6 14977),(.avoidNot 6 0 14977 0),(.avoidNot 6 13 14977 0),(.avoidNot 6 0 14977 1),(.avoidNot 6 13 14977 1),(.avoidNot 6 0 14977 2),(.avoidNot 6 13 14977 2),(.exactAt 6 8 127),(.seeLab 6 8 0 127 0),(.seeLab 6 8 5 127 0),(.seeLab 6 8 0 127 1),(.seeLab 6 8 5 127 1),(.seeLab 6 8 0 127 2),(.seeLab 6 8 5 127 2),(.exactAt 6 8 8297),(.seeLab 6 8 13 8297 0),(.seeLab 6 8 0 8297 1),(.seeLab 6 8 13 8297 2),(.exactAt 6 8 12481),(.seeLab 6 8 0 12481 0),(.seeLab 6 8 13 12481 0),(.seeLab 6 8 13 12481 1),(.seeLab 6 8 0 12481 2),(.seeLab 6 8 13 12481 2),(.diffC 0 6 5),(.residual 6 5 0 1),(.residual 6 5 0 2),(.residual 6 5 1 2),(.resCommon 6 9 0),(.diffC 0 6 13),(.resCommon 6 13 0),(.residual 6 13 0 1),(.residual 6 13 0 2),(.residual 6 13 1 2),(.self 7 0),(.self 7 1),(.self 7 2),(.exposure 8 541),(.avoidNot 8 9 541 0),(.exposure 8 2087),(.avoidNot 8 11 2087 0),(.self 9 0),(.earlier 9 0),(.labCommon 9 11 0),(.self 9 1),(.earlier 9 1),(.labCommon 9 11 1),(.self 9 2),(.labCommon 9 11 2),(.someRes 9),(.exposure 9 245),(.avoidNot 9 6 245 0),(.avoidNot 9 7 245 0),(.avoidNot 9 6 245 1),(.avoidNot 9 7 245 1),(.avoidNot 9 6 245 2),(.avoidNot 9 7 245 2),(.exposure 9 2213),(.avoidNot 9 7 2213 0),(.avoidNot 9 11 2213 0),(.avoidNot 9 7 2213 1),(.avoidNot 9 11 2213 1),(.avoidLive 9 2213 2),(.exposure 9 4309),(.avoidNot 9 7 4309 0),(.avoidNot 9 12 4309 0),(.avoidNot 9 7 4309 1),(.avoidNot 9 12 4309 1),(.avoidLive 9 4309 2),(.exactAt 9 1 6789),(.seeLab 9 1 7 6789 0),(.seeLab 9 1 11 6789 0),(.seeLab 9 1 7 6789 1),(.seeLab 9 1 11 6789 1),(.seeLive 9 1 6789 2),(.diffC 0 9 6),(.residual 9 6 0 1),(.residual 9 6 0 2),(.residual 9 6 1 2),(.exposure 10 541),(.avoidNot 10 9 541 0),(.exposure 10 4183),(.avoidNot 10 12 4183 0),(.self 11 0),(.self 11 1),(.earlier 11 1),(.self 11 2),(.exposure 11 5008),(.avoidNot 11 7 5008 0),(.avoidNot 11 9 5008 0),(.avoidNot 11 7 5008 1),(.avoidNot 11 9 5008 1),(.avoidLive 11 5008 2),(.avoidNot 11 7 5008 2),(.avoidNot 11 9 5008 2),(.exposure 11 13504),(.avoidNot 11 7 13504 0),(.avoidLive 11 13504 1),(.avoidLive 11 13504 2),(.exactAt 11 3 6789),(.seeLab 11 3 7 6789 0),(.seeLab 11 3 9 6789 0),(.seeLab 11 3 7 6789 1),(.seeLab 11 3 9 6789 1),(.seeLive 11 3 6789 2),(.seeLab 11 3 7 6789 2),(.seeLab 11 3 9 6789 2),(.diffC 0 11 9),(.residual 11 9 0 1),(.residual 11 9 0 2),(.residual 11 9 1 2),(.self 12 0),(.self 12 1),(.self 12 2),(.someRes 13),(.exposure 13 245),(.avoidNot 13 7 245 0),(.avoidNot 13 7 245 1),(.avoidLive 13 245 2),(.exactAt 13 1 8417),(.seeLab 13 1 6 8417 0),(.seeLab 13 1 7 8417 0),(.seeLab 13 1 6 8417 1),(.seeLab 13 1 7 8417 1),(.seeLive 13 1 8417 2),(.readerAny false 2),(.readerAny false 3),(.readerLab false 3 0 5 false),(.readerAny false 4),(.readerAny false 7),(.readerAny false 8),(.readerAny false 13),(.readerLab false 13 0 5 true),(.readerLab false 13 1 5 true),(.readerLive false 13 2),(.readerLab false 13 2 5 true),(.readerAny false 14),(.readerLive false 14 2),(.readerAny false 15),(.readerLive false 15 2),(.readerAny false 16),(.readerLive false 16 2),(.readerAny false 17),(.readerLive false 17 2),(.readerAny false 18),(.readerLive false 18 2),(.readerAny true 2),(.readerLab true 2 0 7 true),(.readerLab true 2 1 7 true),(.readerLab true 2 2 7 true),(.readerAny true 3),(.readerLab true 3 0 6 true),(.readerLab true 3 0 7 false),(.readerLab true 3 1 6 true),(.readerLab true 3 1 7 false),(.readerLive true 3 2),(.readerLab true 3 2 6 true),(.readerLab true 3 2 7 false),(.readerAny true 4),(.readerLab true 4 0 6 false),(.readerLab true 4 0 7 false),(.readerLab true 4 1 6 false),(.readerLab true 4 1 7 false),(.readerLive true 4 2),(.readerAny true 7),(.readerLab true 7 0 7 true),(.readerLab true 7 1 7 true),(.readerLab true 7 2 7 true),(.readerAny true 8),(.readerLab true 8 0 7 false),(.readerLive true 8 1),(.readerLive true 8 2),(.readerAny true 13),(.readerLab true 13 0 9 true),(.readerLab true 13 0 12 false),(.readerLab true 13 1 9 true),(.readerLab true 13 1 12 false),(.readerLive true 13 2),(.readerAny true 14),(.readerLab true 14 0 9 false),(.readerLab true 14 0 12 false),(.readerAny true 15),(.readerLab true 15 0 12 true),(.readerLab true 15 1 12 true),(.readerLab true 15 2 12 true),(.readerAny true 16),(.readerLab true 16 0 9 false),(.readerLab true 16 0 11 false),(.readerAny true 17),(.readerLab true 17 0 9 true),(.readerLab true 17 0 11 false),(.readerLab true 17 1 9 true),(.readerLab true 17 1 11 false),(.readerLive true 17 2),(.readerLab true 17 2 9 true),(.readerLab true 17 2 11 false),(.readerAny true 18),(.readerLab true 18 0 11 true),(.readerLab true 18 1 11 true),(.readerLab true 18 2 11 true),(.gateEq false 2 3 0),(.eqLab true 2 3 7 true),(.gateEq false 2 4 0),(.eqLab true 2 4 7 true),(.gateEq false 3 4 0),(.eqLab true 3 4 6 true),(.eqLab false 3 13 5 false),(.gateEq true 3 13 0),(.gateEq true 3 13 1),(.gateEq false 7 8 0),(.eqLab true 7 8 7 true),(.gateEq false 13 14 0),(.gateEq false 13 14 1),(.eqLab true 13 14 9 true),(.gateEq false 13 15 0),(.gateEq false 13 15 1),(.eqLab true 13 15 12 false),(.gateEq false 14 15 0),(.gateEq false 14 15 1),(.eqLab true 14 15 12 false),(.gateEq false 16 17 0),(.gateEq false 16 17 1),(.eqLab true 16 17 9 false),(.gateEq false 16 18 0),(.gateEq false 16 18 1),(.eqLab true 16 18 11 false),(.gateEq false 17 18 0),(.gateEq false 17 18 1),(.eqLab true 17 18 11 false)]

def table1290_0 : List Nat := [705,0x40282,833,0x441,0x541,0x8482,0xf010003,0xb8882,0x18882,0x35198c43,0xc0c02,0xd0c02,0x130c82,0x150d02,0x160d02,0x3b1c8dc3]
def table1290_1 : List Nat := [0xd0d82,0x120e02,0x160e82,0x411f8f43,0xc0f02,0xf0f02,0x120f82,0x140f82,0x151002,0x171002,0x472290c3,0xc9082,0xd1082,0x129102,0x131102,0x159182]
def table1290_2 : List Nat := [0x161182,0x4d259243,0xf1202,0x129282,0x171302,0x532893c3,0xc9382,0xf1382,0x141402,0x159482,0x171482,0x1502,0x1544e1b0b0385,0x1545a1b110385,0x1545a27110385,0x1d020083]
def table1290_3 : List Nat := [0x31582,0x21030083,0x15c521f0b0805,0x15c5e1f110805,0x15c5e29110805,0x1641,0x16c1,0x1741,0x18c1,0x2f1882,0x1941,0x301902,0x19c1,0x359a02,0x73381a83,0x1dc1]
def table1290_4 : List Nat := [0x349e02,0x733f1a03,0x20c1,0x73441e03,0x29e02,0x8f46a2c3,0x362282,0x372282,0x3d2302,0x3e2302,0x422382,0x432382,0x9549a443,0x372402,0x382402,0x3e2482]
def table1290_5 : List Nat := [0x3f2482,0x3ca502,0x9b4ca5c3,0x372582,0x3a2582,0x3e2602,0x402602,0x3ca682,0xa14fa743,0x37a702,0x382702,0x3ea782,0x3f2782,0x3ca802,0x12882,0x28cf66d340705]
def table1290_6 : List Nat := [0x28d0a6d3c0705,0x28d0a7b3c0705,0x2a41,0x522a02,0x2ac1,0x532a82,0x2b41,0x2d41,0x57ad82,0x2f41,0xc762b0c3,0x583082,0x593082,0x5c3102,0x5d3102,0x5bb182]
def table1290_7 : List Nat := [0x5f3182,0x603182,0xcd65b243,0x583202,0x57b282,0x5bb302,0xd368b3c3,0x58b382,0x593382,0x5cb402,0x5d3402,0x5bb482,0x5fb482,0x603482,0x23502,0x35576b3571c85]
def table1290_8 : List Nat := [0x35582b35b1c85,0x35582bb5b1c85,0x35c1,0x3641,0x36c1,0x3b802,0xeb74b9c3,0x6f3982,0x723a02,0x70ba82,0xf177bb43,0x6e3b02,0x6fbb02,0x713b82,0x72bb82,0x70bc02]
def table1290_9 : List Nat := [0x3cc1,0x3d41,0xf604bd03,0x3e41,0x3ec1,0x3f41,0x10380bfc3,0x105063f83,0x105084003,0x9c082,0x1050a4083,0x10b84c1c3,0x9c282,0x11187c343,0x9c402,0x1178ac4c3]
def table1290_10 : List Nat := [0x11c582,0x11d8dc643,0x11c702,0x12390c7c3,0x11c882,0x12993c943,0x12b2c4903,0x12b2d4983,0x12b2e4a03,0x13197cb43,0x133364b03,0x13437cb03,0x1333d4b83,0x1343ecb83,0x3ccc02,0x133424c03]
def table1290_11 : List Nat := [0x13443cc03,0x13b9ccdc3,0x13c6ecd83,0x13e6fcd83,0x13c71ce03,0x13e72ce03,0x70ce82,0x145a1d043,0x1472c5003,0x1472d5083,0x1472e5103,0x14da5d243,0x14e58d203,0x57d282,0x5bd302,0x155a9d443]
def table1290_12 : List Nat := [0x157335403,0x1583ad403,0x1573b5483,0x15840d483,0x3cd502,0x56c1,0x15c52d683,0x15e53d683,0x165b1d843,0x1676b5803,0x1676c5883,0x1676d5903,0x5a41,0x16a2fda03,0x16c30da03,0x173b8dbc3]
def table1290_13 : List Nat := [0x175335b83,0x17638db83,0x1753b5c03,0x1763fdc03,0x3cdc82,0x175415c83,0x17644dc83,0x17dbdde43,0x17f565e03,0x17f5a5e83,0x17f5e5f03,0x1817a3c83,0x135956003,0x1837c3c83,0x13f956083,0x1857c3d03]
def table1290_14 : List Nat := [0x13d996103,0x1047be183,0x187a84b03,0x187a94b83,0x1897e3e83,0x14fa36203,0x18b833f83,0x18b844003,0x15dab6283,0x18d863f83,0x18d874003,0x166ace303,0x18f864183,0x18f874203,0x166afe383,0x1918c4483]
def table1290_15 : List Nat := [0x1918d4503,0x174b5e403,0x1938f4483,0x193904503,0x17eb6e483,0x1958f4603,0x195904683,0x17ebbe503,513,0x1781,0x1801,0x2901,0x2981,0x3d81,0x82bf82,0x82c002]
def table1290_16 : List Nat := [0x82c082,0x95c902,0x95c982,0x95ca02,0xa3d002,0xa3d082,0xa3d102,0xabd402,0xabd482,0x5701,0x5781,0xb3d802,0xb3d882,0xb3d902,0x5a81,0x5b01]
def table1290_17 : List Nat := [0xbadb82,0xbadc02,0xbadc82,0xbfde02,0xbfde82,0xbfdf02,0x6041,0x9aca82,0x60c1,0x9fca82,0x6141,0x9ecc82,0x826182,0x6241,0xa7d182,0xab6282]
def table1290_18 : List Nat := [0xb36382,0xba6402,0xbf6482,0x5fc1,0x6481,0x5d41,0x6401,0x59c1,0x6381,0x4141,0x6181,0x354e4b661b485,0x354e4ae69b105,0x1aa725b30c4,0xd5392d83,0x1aa72a73084]
def table1290_19 : List Nat := [0xd5393103,0x51c1,0x53c1,0x1763c1cc3,0x6a9c82,0xbb1e02,0x3c9f82,0x5d81,0x6501,0x4ac1,0x4d41,0x4fc1,0xae22101484,0x15c2c20298f05,0xae22100f84,0x30882]
def table1290_20 : List Nat := [0x11c802,0x8c1,0x5c1,193,385,0x2881,0x3801,0x3a81,0x3c01,0x4e81,0x9e4e02,0x9e4d82,0x4f01,0x4c81,0x310d8003,0x3178d09c384]
def table1290_21 : List Nat := [0x18bc684c3,0x238683,0x11c2,1,0x481,0xaad5c2,0x3cd402,0x1e41,0x1a41,321,0x741,0x4b01,0x4c01,0x4bc1,0x1f41,0x1e81]
def table1290_22 : List Nat := [0x2301,0x2141,0x1b41,0x2381,0x2281]

def encoded1290 (i : Nat) : Nat :=
  if i < 176 then
    if i < 80 then
      if i < 32 then
        if i < 16 then
          table1290_0.getD (i%16) 0
        else
          table1290_1.getD (i%16) 0
      else
        if i < 48 then
          table1290_2.getD (i%16) 0
        else
          if i < 64 then
            table1290_3.getD (i%16) 0
          else
            table1290_4.getD (i%16) 0
    else
      if i < 128 then
        if i < 96 then
          table1290_5.getD (i%16) 0
        else
          if i < 112 then
            table1290_6.getD (i%16) 0
          else
            table1290_7.getD (i%16) 0
      else
        if i < 144 then
          table1290_8.getD (i%16) 0
        else
          if i < 160 then
            table1290_9.getD (i%16) 0
          else
            table1290_10.getD (i%16) 0
  else
    if i < 272 then
      if i < 224 then
        if i < 192 then
          table1290_11.getD (i%16) 0
        else
          if i < 208 then
            table1290_12.getD (i%16) 0
          else
            table1290_13.getD (i%16) 0
      else
        if i < 240 then
          table1290_14.getD (i%16) 0
        else
          if i < 256 then
            table1290_15.getD (i%16) 0
          else
            table1290_16.getD (i%16) 0
    else
      if i < 320 then
        if i < 288 then
          table1290_17.getD (i%16) 0
        else
          if i < 304 then
            table1290_18.getD (i%16) 0
          else
            table1290_19.getD (i%16) 0
      else
        if i < 336 then
          table1290_20.getD (i%16) 0
        else
          if i < 352 then
            table1290_21.getD (i%16) 0
          else
            table1290_22.getD (i%16) 0
def book1290 (i : Nat) : Clause := let n := encoded1290 i; unpackLits 9 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClauses1290 : inputsOK 1 1290 a1290 r1290 (baseBook book1290 248).toList=true := by decide +kernel

def rows1290_0 : List Nat := [513,0xe07201,0xe87601,0x188c601,0x190ca01,0x7c2452402,0x92e01,0xd3001,0x113401,0xd54c01,0xd94e01,0xdd5001,0xd57001,0xd97201,0xdd7401,0xf18001,0xfd8401,0x7db158c02,0x7e3158e02,0x2099201,0x20d9401,0x2119601,0x7cb319a02,0x7d3319c02]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk1290_0 : checkRows book1290 9 248 rows1290_0=true := by decide +kernel

def rows1290_1 : List Nat := [0xf1a001,0xfda401,0x109aa01,0x199b001,0x19db201,0x1a5b401,0x48a41b602,0x459b801,0x49a41ba02,0x461bc01,0x49a45be02,0x469c001,0x3f5c201,0x4aa51c802,0x475ca01,0x425d001,0x429dc01,0x439e201,0x43de801,0x1158a44dae03,0x48e4401,0x11288c419e03,0x4964201,0x10d8642d9003]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk1290_1 : checkRows book1290 9 272 rows1290_1=true := by decide +kernel

def rows1290_2 : List Nat := [0x49e4001,0x1007fbf92c03,0x4a63801,0x1a902703e9f0dc05,0x1d8fe79371b4f005,0x1e8f081401c4d52c959a0ec09,0x1f4f4803f9dcd86b969a0ec09,0xbd3d2ececbc3b9b0d67b5f4b8fe0b,0x3b9c8ec743ccb0da753dcb8e60a,0x10682c116e03,0x4c63c01,0x1a2d36b0f882431e9019e08,0x1be5f30974c8d405,0x1333f1126803,0x4d2c130b85028974b207,0x13cb04c2d139a2cf69cd9a85d28cd4b60d,0x91cddee02,0x103814054a03,0x4e62e01,0x4e63201,0x150b8cc6818150a42607,0x9464260a8505005,0x4424190d046170b01c4208,0x9c50331a064273e9ecf06208038c04a0d]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk1290_2 : checkRows book1290 9 296 rows1290_2=true := by decide +kernel

def rows1290_3 : List Nat := [0x2853ef679a8145269c491de09,0x1429f7abc947405228941269c491e00c,0x5040e01,0x5041001,0x5067e01,0x50cbc01,0x5110a01,0x5191201,0x5191e01,0x5196c01,0x46219148846ad5693ba451d0e0a,0x47219148745acd653ba451d100a,0xb1a55269603,0x5323601,0x38182d160185741a150c1209,0x9b4b3b5d4994e4a1cc07,0x4da59d8e94ed3d3c9c4cca1ce0a,0x1e2e088783a1a0e0405606a0d0c240c,0xd0283d4e165445606a150c360a,0x160c168b81a200fd480c2ba0d0c120c,0x54c0a01,0x8441d7e02,0x2b4a4a92a3898257573aea11faab12752a93d50aa11,0xab292a4ace361afeaceba847eaac45715e752a93d50a613]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk1290_3 : checkRows book1290 9 320 rows1290_3=true := by decide +kernel

def rows1290_4 : List Nat := [0x55c8001,0x55c8801,0xa1d645e02,0x12890602f91d54ababd6a8b58a6ce88a0d,0x904625984c0b057d5eb5459d5348a0c,0xadd715202,0x9d5755a02,0xa6d755802,0x5789201,0x28b5aabd7cc204,0x28b5aac57cbe04,0x5849401,0x5888c01]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk1290_4 : checkRows book1290 9 344 rows1290_4=true := by decide +kernel

def lastUnits1290 := digits 9 3 0x582c963
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflict1290 : checkReasons book1290 357 69 lastUnits1290 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem exclude1290 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 1290=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=1) h hc bp eq (by decide +kernel)
  let v := truth Z a1290
  have hbase : ValidThrough v book1290 248 := book_start Z h hc z eq _ _ _ _ initialClauses1290
  have h0 : ValidThrough v book1290 272 := rows_sound hbase rows1290_0 rowsOk1290_0
  have h1 : ValidThrough v book1290 296 := rows_sound h0 rows1290_1 rowsOk1290_1
  have h2 : ValidThrough v book1290 320 := rows_sound h1 rows1290_2 rowsOk1290_2
  have h3 : ValidThrough v book1290 344 := rows_sound h2 rows1290_3 rowsOk1290_3
  have h4 : ValidThrough v book1290 357 := rows_sound h3 rows1290_4 rowsOk1290_4
  exact book_end h4 _ _ conflict1290
end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
