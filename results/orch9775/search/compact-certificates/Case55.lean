import CompactFramework

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.Outside.L_meta_9775.UpstreamCore.Resolution

def a55 : Array Fact := #[(.res 0 8),(.res 1 8),(.res 0 9),(.res 1 9),(.res 0 13),(.res 1 13),(.lab 1 0 1),(.lab 2 0 2),(.lab 2 0 1),(.avoid 2 314 0),(.lab 4 0 1),(.lab 4 0 2),(.avoid 4 1102 0),(.live 8 1),(.lab 8 0 9),(.common 8 9),(.lab 8 0 10),(.lab 8 0 13),(.common 8 13),(.live 8 2),(.lab 8 1 9),(.lab 8 1 10),(.lab 8 1 13),(.live 8 3),(.lab 8 2 9),(.lab 8 2 10),(.lab 8 2 13),(.lab 8 3 10),(.lab 8 3 13),(.avoid 8 1548 0),(.avoid 8 1548 1),(.avoid 8 1548 2),(.avoid 8 1548 3),(.avoid 8 9288 0),(.avoid 8 9288 1),(.avoid 8 9288 2),(.avoid 8 9288 3),(.see 8 0 1290 0),(.see 8 0 1290 1),(.see 8 0 1290 2),(.see 8 0 1290 3),(.see 8 0 9992 0),(.see 8 0 9992 1),(.see 8 0 9992 2),(.see 8 0 9992 3),(.see 8 0 16256 0),(.see 8 0 16256 1),(.see 8 0 16256 2),(.see 8 0 16256 3),(.see 8 2 9992 0),(.see 8 2 9992 1),(.see 8 2 9992 2),(.see 8 2 9992 3),(.diff 0 8 9),(.diff 1 8 9),(.diff 0 8 13),(.diff 1 8 13),(.lab 9 0 7),(.lab 9 0 12),(.common 9 13),(.live 9 2),(.lab 9 1 7),(.lab 9 1 12),(.live 9 3),(.avoid 9 4309 0),(.avoid 9 4309 1),(.avoid 9 4309 2),(.avoid 9 4309 3),(.see 9 1 4757 0),(.see 9 1 4757 1),(.see 9 1 4757 2),(.see 9 1 4757 3),(.see 9 5 5008 0),(.see 9 5 5008 1),(.see 9 5 5008 2),(.see 9 5 5008 3),(.live 13 1),(.lab 13 0 8),(.lab 13 0 9),(.live 13 2),(.lab 13 1 8),(.lab 13 1 9),(.live 13 3),(.lab 13 2 8),(.lab 13 2 9),(.avoid 13 792 0),(.avoid 13 792 1),(.avoid 13 792 2),(.avoid 13 792 3),(.see 13 1 9992 0),(.see 13 1 9992 1),(.see 13 1 9992 2),(.see 13 1 9992 3),(.see 13 2 9992 0),(.see 13 2 9992 1),(.see 13 2 9992 2),(.see 13 2 9992 3),(.diff 0 13 8),(.diff 1 13 8),(.diff 0 13 9),(.diff 1 13 9),(.reader false 4 0),(.es false 4 1),(.reader false 6 0),(.es false 6 1),(.es false 6 2),(.reader false 12 0),(.es false 12 1),(.es false 12 2),(.reader true 4 0),(.reader true 4 1),(.reader true 4 2),(.reader true 4 3),(.reader true 6 0),(.reader true 6 1),(.reader true 6 2),(.reader true 6 3),(.reader true 12 0),(.reader true 12 1),(.reader true 12 2),(.reader true 12 3),(.gate 4 6),(.gate 4 12),(.gate 6 12)]
def r55 : List Scheme := [(.self 1 0),(.self 2 0),(.exposure 2 314),(.avoidNot 2 1 314 0),(.exposure 4 1102),(.avoidNot 4 1 1102 0),(.avoidNot 4 2 1102 0),(.earlier 8 1),(.earlier 8 2),(.allRes 8 0),(.allRes 8 1),(.exposure 8 1548),(.avoidNot 8 9 1548 0),(.avoidNot 8 10 1548 0),(.avoidNot 8 9 1548 1),(.avoidNot 8 10 1548 1),(.avoidNot 8 9 1548 2),(.avoidNot 8 10 1548 2),(.avoidLive 8 1548 3),(.exposure 8 9288),(.avoidNot 8 10 9288 0),(.avoidNot 8 13 9288 0),(.avoidNot 8 10 9288 1),(.avoidNot 8 13 9288 1),(.avoidLive 8 9288 2),(.avoidNot 8 10 9288 2),(.avoidNot 8 13 9288 2),(.avoidLive 8 9288 3),(.avoidNot 8 10 9288 3),(.avoidNot 8 13 9288 3),(.exactAt 8 0 1290),(.seeLab 8 0 10 1290 0),(.seeLab 8 0 10 1290 1),(.seeLive 8 0 1290 2),(.seeLive 8 0 1290 3),(.exactAt 8 0 9992),(.seeLab 8 0 9 9992 0),(.seeLab 8 0 10 9992 0),(.seeLab 8 0 13 9992 0),(.seeLab 8 0 9 9992 1),(.seeLab 8 0 10 9992 1),(.seeLab 8 0 13 9992 1),(.seeLab 8 0 9 9992 2),(.seeLab 8 0 10 9992 2),(.seeLab 8 0 13 9992 2),(.seeLive 8 0 9992 3),(.seeLab 8 0 10 9992 3),(.seeLab 8 0 13 9992 3),(.exactAt 8 0 16256),(.seeLab 8 0 13 16256 0),(.seeLab 8 0 13 16256 1),(.seeLab 8 0 10 16256 2),(.seeLive 8 0 16256 3),(.exactAt 8 2 9992),(.seeLab 8 2 10 9992 0),(.seeLab 8 2 13 9992 0),(.seeLab 8 2 10 9992 1),(.seeLab 8 2 13 9992 1),(.seeLive 8 2 9992 2),(.seeLive 8 2 9992 3),(.diffX 0 8 9),(.diffC 0 8 9),(.resCommon 8 9 0),(.diffX 1 8 9),(.diffC 1 8 9),(.resCommon 8 9 1),(.residual 8 9 0 1),(.residual 8 9 0 2),(.residual 8 9 1 2),(.diffX 0 8 13),(.diffC 0 8 13),(.diffX 1 8 13),(.diffC 1 8 13),(.adjacentCommon 8 13 2),(.residual 8 13 0 1),(.residual 8 13 0 2),(.residual 8 13 0 3),(.residual 8 13 1 2),(.residual 8 13 1 3),(.residual 8 13 2 3),(.someRes 9),(.allRes 9 1),(.exposure 9 4309),(.avoidNot 9 7 4309 0),(.avoidNot 9 12 4309 0),(.avoidNot 9 7 4309 1),(.avoidNot 9 12 4309 1),(.avoidLive 9 4309 2),(.avoidLive 9 4309 3),(.exactAt 9 1 4757),(.seeLab 9 1 7 4757 0),(.seeLab 9 1 7 4757 1),(.seeLive 9 1 4757 2),(.seeLive 9 1 4757 3),(.exactAt 9 5 5008),(.seeLab 9 5 7 5008 0),(.seeLab 9 5 12 5008 0),(.seeLab 9 5 7 5008 1),(.seeLab 9 5 12 5008 1),(.seeLive 9 5 5008 2),(.seeLive 9 5 5008 3),(.adjacentCommon 9 13 1),(.earlier 13 1),(.allRes 13 0),(.allRes 13 1),(.exposure 13 792),(.avoidNot 13 8 792 0),(.avoidNot 13 9 792 0),(.avoidNot 13 8 792 1),(.avoidNot 13 9 792 1),(.avoidNot 13 8 792 2),(.avoidNot 13 9 792 2),(.avoidLive 13 792 3),(.exactAt 13 1 9992),(.seeLab 13 1 8 9992 0),(.seeLab 13 1 9 9992 0),(.seeLab 13 1 8 9992 1),(.seeLab 13 1 9 9992 1),(.seeLab 13 1 8 9992 2),(.seeLab 13 1 9 9992 2),(.seeLive 13 1 9992 3),(.exactAt 13 2 9992),(.seeLab 13 2 8 9992 0),(.seeLab 13 2 9 9992 0),(.seeLab 13 2 8 9992 1),(.seeLab 13 2 9 9992 1),(.seeLab 13 2 8 9992 2),(.seeLab 13 2 9 9992 2),(.seeLive 13 2 9992 3),(.diffX 0 13 8),(.diffC 0 13 8),(.diffX 1 13 8),(.diffC 1 13 8),(.residual 13 8 0 1),(.residual 13 8 0 2),(.residual 13 8 1 2),(.diffX 0 13 9),(.diffC 0 13 9),(.diffX 1 13 9),(.diffC 1 13 9),(.residual 13 9 0 1),(.residual 13 9 0 2),(.residual 13 9 1 2),(.readerAny false 4),(.readerLab false 4 0 1 true),(.readerAny false 6),(.readerLab false 6 0 1 false),(.readerLab false 6 0 2 true),(.readerAny false 12),(.readerLab false 12 0 1 false),(.readerLab false 12 0 2 false),(.readerAny true 4),(.readerLive true 4 2),(.readerLive true 4 3),(.readerAny true 6),(.readerLive true 6 2),(.readerLive true 6 3),(.readerAny true 12),(.readerLive true 12 2),(.readerLive true 12 3),(.eqLab false 4 6 1 true),(.gateEq true 4 6 0),(.gateEq true 4 6 1),(.eqLab false 4 12 1 true),(.gateEq true 4 12 0),(.gateEq true 4 12 1),(.eqLab false 6 12 2 true),(.gateEq true 6 12 0),(.gateEq true 6 12 1)]

def table55_0 : List Nat := [833,961,0x4c1,0x40482,0x641,0x50602,0x58602,0x6c982,0x9cb82,0x4b82,0xcb82,0x104fcf4ec4,0x70e82,0x80e82,0xa0f02,0xa8f02]
def table55_1 : List Nat := [0xc0f82,0xc8f82,0xbd002,0x1251d150c4,0x81082,0x89082,0xa9102,0xb1102,0x9d182,0xc9182,0xd1182,0xbd202,0xd9202,0xe1202,0x1453d352c4,0x85282]
def table55_2 : List Nat := [0xad302,0x9d382,0xbd402,0x1655d554c4,0x71482,0x85482,0x89482,0xa1502,0xad502,0xb1502,0xc1582,0xcd582,0xd1582,0xbd602,0xdd602,0xe1602]
def table55_3 : List Nat := [0x1857d756c4,0x89682,0xb1702,0xcd782,0xbd802,0x1a59d958c4,0x81882,0x8d882,0xa9902,0xb5902,0x9d982,0xbda02,0x5a82,0x11a82,0x7c10003,0xdb02]
def table55_4 : List Nat := [0x19b02,0x7c18083,0x1b5aca47468786,0x1b5acc47498786,0x1b5acc4a498786,0x5b82,0x21b82,0xdc02,0x29c02,0x941,0x1c5bcb48c68906,0x1c5bcd48c98906,0x1c5bce48cb8906,0x1c5bcd4b498906,0x1c5bce4b4b8906,0x1c5bce4d4b8906]
def table55_5 : List Nat := [0x1c15e03,0x1df82,0x21e160e044,0x1ca002,0x1d2002,0x1ea082,0x1f2082,0x1e6102,0x1fe182,0x23e362e244,0x1ce202,0x1ee282,0x1e6302,0x1fe382,0x25e564e444,0x1ca402]
def table55_6 : List Nat := [0x1d6402,0x1ea482,0x1f6482,0x1e6502,0x1fe582,0x1dc1,0x266782,0x26902,0x2e902,0x2c6beb6ac4,0x26aa82,0x272a82,0x282b02,0x28ab02,0x29ab82,0x2a2b82]
def table55_7 : List Nat := [0x296c02,0x2e6ded6cc4,0x26ac82,0x276c82,0x282d02,0x28ed02,0x29ad82,0x2a6d82,0x296e02,0x306fef6ec4,0x26ee82,0x272e82,0x286f02,0x28af02,0x29ef82,0x2a2f82]
def table55_8 : List Nat := [0x297002,0x27082,0x3082,0x2f102,0xb102,0x3170e866e60906,0x3170e9e6e78906,0x3170e9e8678906,0x27182,0x13182,0x2f202,0x1b202,0x3271e8e7661d86,0x3271ea67679d86,0x3271ea68e79d86,0x32c1]
def table55_9 : List Nat := [0x33433283,0x33c1,0x34047383,0x34c3b383,0x3541,0x35857503,0x3605f503,0x3877f776c4,0x27f782,0x297802,0x3a79f978c4,0x27f982,0x297a02,0x3c7bfb7ac4,0x27fb82,0x297c02]
def table55_10 : List Nat := [0x34733c83,0x3cf8b683,0x3cf93703,0x35f33d03,0x3d7ab683,0x3d7b3703,0x3674bd83,0x3dfab883,0x3dfb3903,0x401,0x501,0x581,0x1c5bcb48c685,0x1c5bcd48c985,0x1c5bce48cb85,0x1c5bcd4b4985]
def table55_11 : List Nat := [0x1c5bce4b4b85,0x1c5bce4d4b85,0x3170e866e605,0x3170e9e6e785,0x3170e9e86785,0x3271e8e76605,0x3271ea676785,0x3271ea68e785,0x3341,0x3401,0x34c1,0x3581,0x3601,0x3c81,0x38b682,0x393702]
def table55_12 : List Nat := [0x3d01,0x3ab682,0x3b3702,0x3d81,0x3ab882,0x3b3902,0x1fde6483,0x1fde42,0x290bd1d484,0x290bcd03,0x290bc983,0x145a53d9d085,0x290bc2,0x291102,0x291082,0x291182]
def table55_13 : List Nat := [0x2901,0x2c01,0x2e01,0x3001,0x3801,0x3a01,0x3c01,0x29a802,0xba62983,0x30f167a9c4,0xba782,0x27fb02,0x27c1,0x2641,0xb81,0x1001]
def table55_14 : List Nat := [0x1201,0x1401,0x1601,0x1a01,0x11554883,0x1089c2,0x1ac08c4fc98186,0x1170a768c088d587,0x1ac0874ec98186,0x1170a768c09546,0x115bcb499c45,0x141c2,0x1170a768c08986,0x1149c2,0x11499bdc44,0x2febe703]
def table55_15 : List Nat := [0x116ff0abc4,0x99ac0819585,0x99adb479505,0x99ac08184,0x116ff083,0x99b5ac79485,0x99b5ac784,0x99b400104,0x2ff1f26884,0x31eff243,0x1169c2,0x29afc2,0x1166f203,0x116a82,0x1141,0xa81]
def table55_16 : List Nat := [0xb01,0x1301,0x1501,0x1901,0x26c1898084,0x26f18983,0x9c1,0x6c1,0x2af1f243,0x1c5bc2,0x2ae6c2,0x2ae982,0x2701,0x2af102,0x2ff082,0x29c1]
def table55_17 : List Nat := [0x2801,0x2fc1,0x2ac1,0x2a01,0x2681,0x3181,0x3241,705,385,0x1c01,321,0x1bc1,65,0x3081,0x1b41,0x3141]
def table55_18 : List Nat := [193]

def encoded55 (i : Nat) : Nat :=
  if i < 144 then
    if i < 64 then
      if i < 32 then
        if i < 16 then
          table55_0.getD (i%16) 0
        else
          table55_1.getD (i%16) 0
      else
        if i < 48 then
          table55_2.getD (i%16) 0
        else
          table55_3.getD (i%16) 0
    else
      if i < 96 then
        if i < 80 then
          table55_4.getD (i%16) 0
        else
          table55_5.getD (i%16) 0
      else
        if i < 112 then
          table55_6.getD (i%16) 0
        else
          if i < 128 then
            table55_7.getD (i%16) 0
          else
            table55_8.getD (i%16) 0
  else
    if i < 224 then
      if i < 176 then
        if i < 160 then
          table55_9.getD (i%16) 0
        else
          table55_10.getD (i%16) 0
      else
        if i < 192 then
          table55_11.getD (i%16) 0
        else
          if i < 208 then
            table55_12.getD (i%16) 0
          else
            table55_13.getD (i%16) 0
    else
      if i < 256 then
        if i < 240 then
          table55_14.getD (i%16) 0
        else
          table55_15.getD (i%16) 0
      else
        if i < 272 then
          table55_16.getD (i%16) 0
        else
          if i < 288 then
            table55_17.getD (i%16) 0
          else
            table55_18.getD (i%16) 0
def book55 (i : Nat) : Clause := let n := encoded55 i; unpackLits 8 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClauses55 : inputsOK 2 55 a55 r55 (baseBook book55 169).toList=true := by decide +kernel

def rows55_0 : List Nat := [0x80601,0x100a01,0x100c01,0x1249401,0x1249601,0x1249801,0x1249a01,0x1249c01,0x1249e01,0x1250a01,0x1250c01,0x1250e01,0x1951801,0x1951a01,0x1951c01,0x23d2002,0x54a452402,0xa452602,0x552512a02,0x55a512c02,0x5cae14002,0x2f54201,0x2f54401,0x5dae14602]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk55_0 : checkRows book55 9 169 rows55_0=true := by decide +kernel

def rows55_1 : List Nat := [0x3014801,0x3014a01,0x5e2e94c02,0x30d4e01,0x30d5001,0x5a29164ac5b31184b05d2b970a60b,0x5b29164a85a3017cbcc631970ae582e990aa0f,0xe35560e42e131b0504c252319c90680d8ec7410,0x1c6aac1b85426380b0a45023640b0344633920d01b168ec7415,0x6613180c42a320bab55e4633920d01b1a3243210,0x201a8786e1f0a8507007,0x3e350f0e440170b04d963a10861943b1106c6c10,0x4c2f162b160af1405c2c4633920d007043304610,0x522f162b15cad12854284633920d007043304610,0x26148bd5aaf588ac34192319c906804330460f,0x130a458ae582c45c1d0e04d9ece66b3090463419c4612,0x340e001,0x340f001,0x3410001,0x3413201,0x3413801,0x3413e01,0x1ace2693a1b0dc7669344e609,0x6d389a4e46a5935cec6e41025080a69344ea0f]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk55_1 : checkRows book55 9 193 rows55_1=true := by decide +kernel

def rows55_2 : List Nat := [0x6f389a4e86c391a968b368b48ee0b,0x6c199040942029b206,0x1349762b09309b6ab517c08,0x13497623053adb4f26d30d56a3597e0c,0x370cc01,0x371b401,0x3782401,0x3783601,0x3784401,0x3785a01,0x3787601,0x191184c4c15713805607,0x742171b859604,0xe0611086412037c1607,0x140a2e644ad5144856b942619088b0562a2320478826eb818e15,0x1c102110c824003b7c1608,0x140a2e844ad514485686830130a0344a2411b9dc846408f104dd703898e19,0xa86958af03b802606,0x281458e02,0x181021110824075a256a8a243a80e46408f104271483c50e96fb741618,0xe50c3802603,0x141184c581a56b9052ea703884a0b,0x6c3c9a4f66b69b44f807,0x351e4d27d36bb1de477711902ed69b44f40e]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk55_2 : checkRows book55 9 217 rows55_2=true := by decide +kernel

def rows55_3 : List Nat := [0xe6158a82203,0x40180f22108502703b7c1609,0x3a04a2411bc9e241203881a09,0xfa7b5bad912eb799bde08a2411ddc3c2320902ed69b70f214,0x401c0d219084a2403b7c1609,0x180e0890c882b1508deaf27137c160c,0x1f0f5ec02,0x695b1a8f67a3c9f4dad16e34cde0b,0x37ad56ef86e375de06,0x116eb7ba208c45770fc908441b65e87e76b71f210,0x693a9a8e27a399e5de6e3b1f1aed16934cda0f,0x1fac9ee8222bb9d64845a29dad77d375080e,0xf164f34211ddceb2322510b67e1acd4ed6b9fdf6fa6eb710415,0xf164f34211ddceb2322510b77e1c8e275369a5fa7f7db5cec6e7d3b5badc69345041d,0x3f82c01,0x3f82e01,0x3fc4001,0x3fc5001,0x4007201,0x164d9410f1e6846eb71ae08,0x130b158af23c100e46443ad130271400460e,0x7c6a1e1d08606e380b846c09,0x4180e01,0xd2b7371fcfcf968b70da08]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk55_3 : checkRows book55 9 241 rows55_3=true := by decide +kernel

def rows55_4 : List Nat := [0x9858ac57c1a0107714084609,0x2c9b2841fbdd044584bac908b454220add6e419ae11,0x1b4e2693b1b8e50a69344ea09,0x3a1dcf86f3cbbcfd0b39428f66b6934ce20e,0x210eb443dc8c45848fc908441c19160c,0x1f2eb453cc9047848f08c8240c19120c,0x22deef922c16126a1f9221a8441b661c7e83371d611,0x43dae01,0x43df601,0x43e1601,0x444fe01,0x448d401,0x834520a02,0x2270c6e4556c04,0x4591401,0x4591601,0x45c9001,0x461d601,0x4661201,0x46c8a01,0x4710401,0x1068d471ee03,0x221146ec756404,0x4787e01]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk55_4 : checkRows book55 9 265 rows55_4=true := by decide +kernel

def lastUnits55 := digits 9 2 0x2411f
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflict55 : checkReasons book55 289 132 lastUnits55 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem exclude55 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 55=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=2) h hc bp eq (by decide +kernel)
  let v := truth Z a55
  have hbase : ValidThrough v book55 169 := book_start Z h hc z eq _ _ _ _ initialClauses55
  have h0 : ValidThrough v book55 193 := rows_sound hbase rows55_0 rowsOk55_0
  have h1 : ValidThrough v book55 217 := rows_sound h0 rows55_1 rowsOk55_1
  have h2 : ValidThrough v book55 241 := rows_sound h1 rows55_2 rowsOk55_2
  have h3 : ValidThrough v book55 265 := rows_sound h2 rows55_3 rowsOk55_3
  have h4 : ValidThrough v book55 289 := rows_sound h3 rows55_4 rowsOk55_4
  exact book_end h4 _ _ conflict55
end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
