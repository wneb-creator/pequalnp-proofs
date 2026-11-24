def C1_initial : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]

def C1_values : Nat := 0xffffffccffffff00fffff0f0fffff000ffffccccffffcc00ffffc0c0ffffaaaaffffaa00ffff8888ffff5555ffff0f0ffff0fff0fff0ff00fff00000ffccffccffaaffaaffaaff88ffaaff00ffaa0000ffa0ff00ff88ff88ff33ff00ff0fff0fff00f000ff000000fcfcfcfcfcfcccccfcfc0000fc00fc00fafafafafafa0000faaaf000fa00fa00f8f8f8f8f0f0f0c0f0f0f000f0f0c0c0f0f00000f0a0f0a0f0a0f080f0a0f000f030f000f000f000eeeeeeeeeeeecccceeee0000ee00ee00ececcccce0e0e0e0cccc0000cc88cc88cc00cc00c8c8c8c8c0c0c0c0aaaaaa88aaaaaa00aaaa8888aaaa0000aa00aa00a8a8a8a8a0a0a0a0a0a00000888888885555555533333333333300000f0f0f0f00ff00ff00ff00000000ffff

def C1_patterns : Nat := 0x0

def C1_N : Nat → Nat
  | 2 => 5
  | 3 => 26
  | 4 => 60
  | 5 => 36
  | 6 => 1
  | _ => 0

def C1_counts : Nat → Nat
  | 2 => 0x2003000
  | 3 => 0xd00d000
  | 4 => 0xe02d001
  | 5 => 0x23001
  | 6 => 1
  | _ => 0

def C1_specs : Nat → Nat
  | 2 => 0x201281000
  | 3 => 0x381381000
  | 4 => 0x481501101
  | 5 => 0x601101
  | 6 => 257
  | _ => 0

def C1_seeds : Nat → List Nat
  | 2 => [0x0, 0x8, 0x6]
  | 3 => [0x0, 0x6e41203, 0x1c05c42]
  | 4 => [0x2, 0x34419794070689b0983d0040702c0f, 0x2a6c3902]
  | 5 => [0x2, 0x66382308880301015f008025010, 0x0]
  | 6 => [0x2, 0x0, 0x0]
  | _ => []

def C1_records : Nat → List (List Nat)
  | 2 => [[], [0x3a33e33c3], [0xe170a3281]]
  | 3 => [[], [0x3c36c73d346b6672ed48b20e4e76273cb3c76a7], [0x22383464c6ace0ce091c62858c8068ce0ce0b92c3836a786dd18d09c19e1a3]]
  | 4 => [[0x1f], [0x6a778f61734f29d84f46f6af39756f3178ef32f04f25d1af12f4bb42f1ef4d77af6b741b82f2db46b8cf72f0af5f786f58f50f17e7ef1cf65774f7cf88f44f47b55768f], [0x109c9c62673834e84e2e33739c1536a34eb4e4e3235a13878c70f10e1e19c3a1383]]
  | 5 => [[0x1f], [0x37f8bf0dd6ff87f0fe11f27f71f07f23f2bf1bf5df81f42f53f09f43f02f03f8cf09b0ff1af0df77f39f07715f5bf39786f19f8df], []]
  | 6 => [[0x1f], [], []]
  | _ => []

def C1_S (s j : Nat) : List Nat :=
  qGroupedState C1_initial 3 32 7 C1_patterns C1_values (C1_counts s) (C1_specs s) (C1_records s) j

def C1_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C1_initial (C1_counts s) (C1_specs s) (C1_seeds s) ws
