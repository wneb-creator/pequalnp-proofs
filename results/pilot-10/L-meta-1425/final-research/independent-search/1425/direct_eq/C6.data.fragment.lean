def C6_initial : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]

def C6_values : Nat := 0xffffff00fffff0f0ffffccccffffcc00ffffc0c0ffffaaaaffff5555fff0fff0ffccffccffaaffaaffaaff00ffaa0000ffa0ffa0ff33ff33ff00cc00ff000000fcfcfcfcfc00fc00fafafafafafaf0f0fafa0000faf0faf0fa00fa00f3f3f3f3f0f0c0c0f0f00000f0c0f0c0f0a0f0a0f000f000eeeeeeeeeeeecccceeee0000eeaacc00ee00ee00eaeac0c0e0e0e0e0cccc0000ccc0ccc0cc88cc88cc80cc80cc00cc00c8c8c8c8c8c0c8c0c0c0c0c0aaaa8888aaaa0000aa00aa00a0a0a0a0888888885555ffff555555553f3f3f3f33ff33ff333333330f0f0f0f0c0c0c0c00ff00ff00cc00cc0000ffff0000aaaa

def C6_patterns : Nat := 0x0

def C6_N : Nat → Nat
  | 2 => 2
  | 3 => 23
  | 4 => 82
  | 5 => 34
  | 6 => 1
  | _ => 0

def C6_counts : Nat → Nat
  | 2 => 0x2000000
  | 3 => 0x700c004000
  | 4 => 0x2a027001
  | 5 => 0x21001
  | 6 => 1
  | _ => 0

def C6_specs : Nat → Nat
  | 2 => 0x201000000
  | 3 => 0x401381201000
  | 4 => 0x481581101
  | 5 => 0x401101
  | 6 => 257
  | _ => 0

def C6_seeds : Nat → List Nat
  | 2 => [0x0, 0x0, 0x4, 0x0]
  | 3 => [0x0, 0x4, 0x21881, 0x25b]
  | 4 => [0x2, 0xb1213a024010020026ac0e8f0, 0x2bc2201413684ee534030020c, 0x0]
  | 5 => [0x2, 0x10a1058e4850018b0b, 0x0, 0x0]
  | 6 => [0x2, 0x0, 0x0, 0x0]
  | _ => []

def C6_records : Nat → List (List Nat)
  | 2 => [[], [], [0x1c442d281], []]
  | 3 => [[], [0x70e9655ab4b], [0x510a284c605e2a2319148e4f17850bca29b918a286297928911], [0xa2254385110a8798451108289e62395110a889e1]]
  | 4 => [[0x1f], [0x185efbafd7ba7bc4bc9be5e2ed3e877476cef87cd705e5bc7e84fa770ee87cbbaee45dd78dbbae8796ee576ef16f17cfbd9e5789da97], [0xf1dbc22b50f38e3651126a233511a943f251f3b14e1023a212d432af1ed3cc71436af1ea309344f5e479c712a78cb44ccf4a57950e794e5023a8558f10ea231d609a834d11f349eb511cf48e541ea384d44ad14258a09c304b], []]
  | 5 => [[0x1f], [0x1ff83fdff4f8fd53ea5d1fc7f12e6fcf7f9f3bec7c6dd9fabe8ec6f89fcfe57c7fbff09f6ffafebfdfe17ccf95e], [], []]
  | 6 => [[0x1f], [], [], []]
  | _ => []

def C6_S (s j : Nat) : List Nat :=
  qGroupedState C6_initial 4 32 6 C6_patterns C6_values (C6_counts s) (C6_specs s) (C6_records s) j

def C6_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C6_initial (C6_counts s) (C6_specs s) (C6_seeds s) ws
