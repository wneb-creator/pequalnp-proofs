def C1_initial : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]

def C1_values : Nat := 0xffffffccffffff00fffff0f0fffff000ffffccccffffcc00ffffc0c0ffffaaaaffffaa00ffff8888ffff5555ffff0f0ffff0fff0fff0ff00fff00000ffccffccffaaffaaffaaff88ffaaff00ffaa0000ffa0ff00ff88ff88ff33ff00ff0fff0fff00ffffff00f000ff000000fcfcfcfcfcfcccccfcfc0000fc00fc00fafafafafafa0000faaaf000fa00fa00f8f8f8f8f0f0f0c0f0f0f000f0f0c0c0f0f00000f0a0f0a0f0a0f080f0a0f000f030f000f000f000eeeeeeeeeeeecccceeee0000ee00ee00ececcccce0e0e0e0ccccffffcccc0000cc88cc88cc00cc00c8c8c8c8c0c0c0c0aaaaaa88aaaaaa00aaaa8888aaaa0000aa00aa00a8a8a8a8a0a0a0a0a0a00000888888885555ffff5555555533333333333300000fff0fff0f5f0fff0f0fffff0f0f0fff0f0f0f0f00ff00ff00ff000000f000f0005500ff0000ffff0000f0f00000aaaa00003333000000ff

def C1_patterns : Nat := 0x0

def C1_N : Nat → Nat
  | 2 => 9
  | 3 => 39
  | 4 => 110
  | 5 => 36
  | 6 => 1
  | _ => 0

def C1_counts : Nat → Nat
  | 2 => 0x5004000
  | 3 => 0x201600f000
  | 4 => 0x3103c001
  | 5 => 0x23001
  | 6 => 1
  | _ => 0

def C1_specs : Nat → Nat
  | 2 => 0x201281000
  | 3 => 0x181701581000
  | 4 => 0x681581101
  | 5 => 0x601101
  | 6 => 257
  | _ => 0

def C1_seeds : Nat → List Nat
  | 2 => [0x0, 0xf, 0xc1, 0x0]
  | 3 => [0x0, 0x4720040d001, 0x49d000f805802b0004001, 0x3]
  | 4 => [0x2, 0x7e0ba01c00612c0080901401c078067b6116140fa, 0x78001a2fc026004000800c52e0b601e82600f6075, 0x0]
  | 5 => [0x2, 0x66382308880301015f008025010, 0x0, 0x0]
  | 6 => [0x2, 0x0, 0x0, 0x0]
  | _ => []

def C1_records : Nat → List (List Nat)
  | 2 => [[], [0x5235631a3543], [0x2a2015e7c2a88894230a9201], []]
  | 3 => [[], [0x54346d54b5478478070c75eb7c716b60b55336e667867], [0x1c281af1238440ab540d7904ad1c35ea074cf969ac1c21435e454b940d416937503505070950e11132a3037c40aa060d79e1c45e3], [0x5aa08056a8222]]
  | 4 => [[0x1f], [0xa2f8cf3fd18f7775af30f5ef63b6ef98f2de0af7b794fa0f06f68f6d71ef32f15b02f59b7f742f5cf04f10f78f49723e28f4cf9ef0f796fa6f8ef08f82f857a8f24f3bd34f1d784770f4af6575fb13792f9cf21d51784f45b5eb], [0x10135202b2442b880f6911365a41a448716a81d35075aa174c49cc106a80a7222b508c1c5055d33c75042ab48b8c0a5d022e5060f4052c8056b95131214eb452cc1172d127a641b40834c093bd1535046d4541e51172d507a6bd6284cd6a89d3887505674141e8093a8153a62962441e48a5d322e], []]
  | 5 => [[0x1f], [0x4ffa5f21d89fa1f23e27f3df8bf13f39f41f31f75f9bf5af6bf15f5bf0af0bfa6f15b23f30f21f91f51f1372bf73f517a0f2ffa7f], [], []]
  | 6 => [[0x1f], [], [], []]
  | _ => []

def C1_S (s j : Nat) : List Nat :=
  qGroupedState C1_initial 4 32 7 C1_patterns C1_values (C1_counts s) (C1_specs s) (C1_records s) j

def C1_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C1_initial (C1_counts s) (C1_specs s) (C1_seeds s) ws
