def C4_initial : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]

def C4_values : Nat := 0xffffff00fffff0f0ffffccccffffcc00ffffc0c0ffffaaaaffff8888ffff5555fff0fff0fff00000ffccffccffaaffaaffaa0000ffa0ffa0ff88ff88ff00f000ff00cc00ff000000fcfcfcfcfafafafafafa0000faf0faf0fa00fa00f8f8f8f8f0f0f000f0f0c0c0f0f00000f0a0f0a0f000f000eeeeeeeeeeeecccceeee0000ee00ee00e0e0e0e0ccccffffcccc0000cc88cc88cc00cc00c8c8c8c8c0c0c0c0aaaa8888aaaa0000aa00aa00a0a0a0a0888888885555ffff555577775555555533333333333300000f0f0f0f00ff00ff0000ffff0000aaaa00003333

def C4_patterns : Nat := 0x0

def C4_N : Nat → Nat
  | 3 => 9
  | 4 => 64
  | 5 => 33
  | 6 => 1
  | _ => 0

def C4_counts : Nat → Nat
  | 3 => 0x7002000
  | 4 => 0x19026001
  | 5 => 0x20001
  | 6 => 1
  | _ => 0

def C4_specs : Nat → Nat
  | 3 => 0x381181000
  | 4 => 0x581601101
  | 5 => 0x501101
  | 6 => 257
  | _ => 0

def C4_seeds : Nat → List Nat
  | 3 => [0x0, 0x1, 0x1ad]
  | 4 => [0x2, 0xb4f400b002013005154040826053, 0xcf1218050040400080b]
  | 5 => [0x2, 0xd8837941a030028400a, 0x0]
  | 6 => [0x2, 0x0, 0x0]
  | _ => []

def C4_records : Nat → List (List Nat)
  | 3 => [[], [0x971ee], [0x3c7a8f1d93bc39cf35cd8cf1547886]]
  | 4 => [[0x1f], [0x1879ef8363f62deafcde2ece7e8f9ef55dfdc37c1e47a8bd6f09eabe9b89719f1bdedb9b3dcb6d1edcfc5e0bd3e9fe29ebdd9786f], [0x70ab1033ea7bb51dba90e1c368e256f6e6716e1c5ceaf2c81f87087d443901b8719a286bd6739c438e1dba8ab204b102e85127810e]]
  | 5 => [[0x1f], [0xde47a4f99fdbf7fd2feff37e2fcef87fb3e3ff5fb7f39f6fd0fb5f77e25f2f89fd5f37c8fa9f1fa2ecbfcbf], []]
  | 6 => [[0x1f], [], []]
  | _ => []

def C4_S (s j : Nat) : List Nat :=
  qGroupedState C4_initial 3 32 6 C4_patterns C4_values (C4_counts s) (C4_specs s) (C4_records s) j

def C4_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C4_initial (C4_counts s) (C4_specs s) (C4_seeds s) ws
