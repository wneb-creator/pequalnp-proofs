def C9_initial : List Nat := [0x21e, 0x41e, 0x7e1, 0x82a, 0x854, 0x1086, 0x1118]

def C9_values : Nat := 0x7afb97d918c575fe6fc379ebcc5ce2e3d718b43567ab31538a8f546293d48698c4a7a50d19e8cc44e1fd6fe173f3979ca8e3e71538798fcc5e62a30f9854c1e52a28f90fc8204001ffcc7c62030f1818c0043e210100040c200010007800c002

def C9_patterns : Nat := 0x1595564156555815565555554554555055155151554551

def C9_N : Nat → Nat
  | 4 => 1
  | 5 => 13
  | 6 => 38
  | 7 => 49
  | 8 => 20
  | 9 => 1
  | _ => 0

def C9_counts : Nat → Nat
  | 4 => 0x1000000
  | 5 => 0x2008003000
  | 6 => 0x201500f000
  | 7 => 0x18018001
  | 8 => 0x10004
  | 9 => 1
  | _ => 0

def C9_specs : Nat → Nat
  | 4 => 0x101000000
  | 5 => 0x181301201000
  | 6 => 0x181501481000
  | 7 => 0x701592111
  | 8 => 0x491312
  | 9 => 273
  | _ => 0

def C9_seeds : Nat → List Nat
  | 4 => [0x0, 0x0, 0x2, 0x0]
  | 5 => [0x0, 0x5, 0x504, 0x3]
  | 6 => [0x0, 0x14a7a1e0e, 0xb4095a00c0e001, 0x1]
  | 7 => [0x2, 0x10101300201205808, 0x56dc00400640248060002, 0x0]
  | 8 => [0x1e, 0x4c0180509, 0x0, 0x0]
  | 9 => [0x2, 0x0, 0x0, 0x0]
  | _ => []

def C9_records : Nat → List (List Nat)
  | 4 => [[], [], [0x6da98], []]
  | 5 => [[], [0x68f33798bc], [0xad459021936c9c5731cc5e58fa3931c0e6d799], [0x36b2731b4a618]]
  | 6 => [[], [0x3bf2e7ae7cb5eb7f2b7a57cc5ec1f0cf877cefe1bf0bf98bc], [0x573bcad85b198f3931e3486584cf1be4f3129e328e5a0c7958af32a1e4863cb28795a6f2ba4ea2674dac73b4a6f131e3e86c], [0x194d0c8920664]]
  | 7 => [[0x7], [0x59466e94a525575324c4ac085316819063175613e45d4290cb1591269555], [0xe0cf8619f174fe1857c74cf89219cc0fe4467c653f860bf1333e502be3ccf8605f0c13e3286ddec7a38bf0c07e2467ca93f8ea7f1033e2e2fc], []]
  | 8 => [[0x7a8c], [0x15cc45d4270dd0749c473dc56e1d3705cc789cc5], [], []]
  | 9 => [[0x7], [], [], []]
  | _ => []

def C9_S (s j : Nat) : List Nat :=
  qGroupedState C9_initial 4 13 6 C9_patterns C9_values (C9_counts s) (C9_specs s) (C9_records s) j

def C9_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C9_initial (C9_counts s) (C9_specs s) (C9_seeds s) ws
