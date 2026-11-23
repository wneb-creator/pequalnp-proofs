def C7_initial : List Nat := [0x750, 0x98d, 0x122b, 0x20f8, 0x2407, 0x4832, 0x50c4]

def C7_values : Nat := 0xe989c31361bec32d1f5a0cb203e0f8b39b63dac6254c4a58948ae8e24f72937f20023a840006c56c8ad6c7ac0753faa3e13fc27574ea0941d27fa4f8480087e1028203040508000dd79a2b2c564cac7ee8f5012002000200010000a000c00140022002000240018002

def C7_patterns : Nat := 0x0

def C7_N : Nat → Nat
  | 5 => 3
  | 6 => 11
  | 7 => 40
  | 8 => 34
  | 9 => 1
  | _ => 0

def C7_counts : Nat → Nat
  | 5 => 0x3000000
  | 6 => 0x9002000
  | 7 => 0x7020001
  | 8 => 0x1c006
  | 9 => 1
  | _ => 0

def C7_specs : Nat → Nat
  | 5 => 0x201000000
  | 6 => 0x281181000
  | 7 => 0x381501101
  | 8 => 0x601302
  | 9 => 257
  | _ => 0

def C7_seeds : Nat → List Nat
  | 5 => [0x0, 0x0, 0x7]
  | 6 => [0x0, 0x1, 0x38a2]
  | 7 => [0x2, 0x2e03804802618010a028, 0x3a5]
  | 8 => [0x7c2, 0x40a80e00780600200221a, 0x0]
  | 9 => [0x2, 0x0, 0x0]
  | _ => []

def C7_records : Nat → List (List Nat)
  | 5 => [[], [], [0x12398b8911f1a87]]
  | 6 => [[], [0x1cecc67], [0x44e66ddc6dbc6cf8613ef997918c71b9c93431b8c66]]
  | 7 => [[0x7f], [0x43ddcfe7bfbbf47db1dd4ef53f7bb99f53ef8f79bf39ded7eff773f2ddec7e7fb37f2bde3f6defcb7d7ed9eec67877b9d97eec6f], [0x1ba6dd32b3bcef68d3e6f319e24f3b89f6]]
  | 8 => [[0x555959565556555565555], [0x7f95fcbfe27fbff8dfdafe17f4bf8bfe0fe9f74ffcbfdefe77f1ffc5ff4ffb7f77fd1fdeee1ff27fd3ff0fe47f], []]
  | 9 => [[0x7f], [], []]
  | _ => []

def C7_S (s j : Nat) : List Nat :=
  qGroupedState C7_initial 3 15 6 C7_patterns C7_values (C7_counts s) (C7_specs s) (C7_records s) j

def C7_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C7_initial (C7_counts s) (C7_specs s) (C7_seeds s) ws
