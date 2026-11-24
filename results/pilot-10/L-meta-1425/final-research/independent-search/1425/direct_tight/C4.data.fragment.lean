def C4_initial : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]

def C4_values : Nat := 0xffffff00fffff0f0ffffccccffffcc00ffffc0c0ffffaaaaffff8888ffff5555fff0fff0fff00000ffccffccffaaffaaffaa0000ffa0ffa0ff88ff88ff00f000ff00cc00ff000000fcfcfcfcfafafafafafa0000faf0faf0fa00fa00f8f8f8f8f0f0f000f0f0c0c0f0f00000f0a0f0a0f000f000eeeeeeeeeeeecccceeee0000ee00ee00e0e0e0e0cccc0000cc88cc88cc00cc00c8c8c8c8c0c0c0c0aaaa8888aaaa0000aa00aa00a0a0a0a0888888885555555533333333333300000f0f0f0f00ff00ff0000ffff

def C4_patterns : Nat := 0x0

def C4_N : Nat → Nat
  | 3 => 5
  | 4 => 35
  | 5 => 33
  | 6 => 1
  | _ => 0

def C4_counts : Nat → Nat
  | 3 => 0x4001000
  | 4 => 0x501d001
  | 5 => 0x20001
  | 6 => 1
  | _ => 0

def C4_specs : Nat → Nat
  | 3 => 0x381101000
  | 4 => 0x201601101
  | 5 => 0x501101
  | 6 => 257
  | _ => 0

def C4_seeds : Nat → List Nat
  | 3 => [0x0, 0x2, 0x21]
  | 4 => [0x2, 0xf0171060110090025c80bc, 0x13]
  | 5 => [0x2, 0xd8837941a030028400a, 0x0]
  | 6 => [0x2, 0x0, 0x0]
  | _ => []

def C4_records : Nat → List (List Nat)
  | 3 => [[], [0x16e], [0x8991c459a9586c96a]]
  | 4 => [[0x1f], [0x33b47783c4794f3fad6e4b97e2dca3ee7ccf4debee5ba5772ef3ef7d2f6f65bdddc7737b15ec7d6f], [0x152d3c223e05b8a1dd832b]]
  | 5 => [[0x1f], [0x5e379ff91fc7f57cefe5f27e1fcaf83f9fe2ff0fadf29f47ccfabf63e15edf85fc1f0fc6fa1f17a1ec7fc1f], []]
  | 6 => [[0x1f], [], []]
  | _ => []

def C4_S (s j : Nat) : List Nat :=
  qGroupedState C4_initial 3 32 6 C4_patterns C4_values (C4_counts s) (C4_specs s) (C4_records s) j

def C4_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C4_initial (C4_counts s) (C4_specs s) (C4_seeds s) ws
