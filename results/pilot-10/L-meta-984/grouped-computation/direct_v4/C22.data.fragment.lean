def C22_initial : List Nat := [0x1d1, 0x2a4, 0x64a, 0x928, 0x1430, 0x2038, 0x3807]

def C22_values : Nat := 0x3d38f0dfc30f01faa7e75f92fe41f887e11f83fe003438d0c2938a4a2838a00264a8af22a487e61d184e20b881e202880820088001d3870c16b4592963057c553052c14703da8e4a2eb0aa427e490020007db1d286ca0fd43a40b902800400080010002800800080010001

def C22_patterns : Nat := 0x0

def C22_N : Nat → Nat
  | 6 => 12
  | 7 => 41
  | 8 => 31
  | 9 => 1
  | _ => 0

def C22_counts : Nat → Nat
  | 6 => 0x9003000
  | 7 => 0x7021001
  | 8 => 0x19006
  | 9 => 1
  | _ => 0

def C22_specs : Nat → Nat
  | 6 => 0x401181000
  | 7 => 0x301481101
  | 8 => 0x581302
  | 9 => 257
  | _ => 0

def C22_seeds : Nat → List Nat
  | 6 => [0x0, 0x1, 0x750a02]
  | 7 => [0x2, 0x285825201e058115e14, 0x4c3]
  | 8 => [0x503, 0x5411a470060d802804, 0x0]
  | 9 => [0x2, 0x0, 0x0]
  | _ => []

def C22_records : Nat → List (List Nat)
  | 6 => [[], [0x613fb9f91f], [0x5e753ae7b5853370ba3d74d9c2b97d623eeae9de5d5]]
  | 7 => [[0x7f], [0x184f6f7e1bf67e8f78afd3f61bf35fbefbdbe4bec6f82ffb7cdf65fdbafdb7f57f65f57dd7ecafb2df3bd93f63becef73dafbd3fba3f], [0x17915e982ee2ecfc5a9fe633f0827d705b]]
  | 8 => [[0x955555665555595655555], [0x67fe7fdf7c3fefff23fc17effe2ff3fff1fe8feb7f53fa1ff7fe0ff83fe7fc4ff57f4bf8ffc2fe37f], []]
  | 9 => [[0x7f], [], []]
  | _ => []

def C22_S (s j : Nat) : List Nat :=
  qGroupedState C22_initial 3 14 6 C22_patterns C22_values (C22_counts s) (C22_specs s) (C22_records s) j

def C22_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C22_initial (C22_counts s) (C22_specs s) (C22_seeds s) ws
