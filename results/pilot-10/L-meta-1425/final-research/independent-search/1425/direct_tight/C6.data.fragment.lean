def C6_initial : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]

def C6_values : Nat := 0xffffff00fffff0f0ffffccccffffcc00ffffc0c0ffffaaaaffff5555fff0fff0ffccffccffaaffaaffaaff00ffaa0000ffa0ffa0ff33ff33ff00cc00ff000000fcfcfcfcfc00fc00fafafafafafaf0f0fafa0000faf0faf0fa00fa00f3f3f3f3f0f0c0c0f0f00000f0c0f0c0f0a0f0a0f000f000eeeeeeeeeeeecccceeee0000eeaacc00ee00ee00eaeac0c0e0e0e0e0cccc0000ccc0ccc0cc88cc88cc80cc80cc00cc00c8c8c8c8c8c0c8c0c0c0c0c0aaaa8888aaaa0000aa00aa00a0a0a0a08888888855555555333333330f0f0f0f00ff00ff0000ffff

def C6_patterns : Nat := 0x0

def C6_N : Nat → Nat
  | 2 => 2
  | 3 => 19
  | 4 => 46
  | 5 => 34
  | 6 => 1
  | _ => 0

def C6_counts : Nat → Nat
  | 2 => 0x2000000
  | 3 => 0x500a004000
  | 4 => 0x1101c001
  | 5 => 0x21001
  | 6 => 1
  | _ => 0

def C6_specs : Nat → Nat
  | 2 => 0x201000000
  | 3 => 0x201381201000
  | 4 => 0x481481101
  | 5 => 0x401101
  | 6 => 257
  | _ => 0

def C6_seeds : Nat → List Nat
  | 2 => [0x0, 0x0, 0x4, 0x0]
  | 3 => [0x0, 0x4, 0x84201, 0x38]
  | 4 => [0x2, 0x22c04010084c18c0, 0x7448081a02, 0x0]
  | 5 => [0x2, 0x10a1058e4850018b0b, 0x0, 0x0]
  | 6 => [0x2, 0x0, 0x0, 0x0]
  | _ => []

def C6_records : Nat → List (List Nat)
  | 2 => [[], [], [0x162c2a1c1], []]
  | 3 => [[], [0x58e664faa8b], [0x23613630538aa16561a463996978e89c5c682e391c5], [0x1648c8cce2c391c584e24621c5921]]
  | 4 => [[0x1f], [0x2bc5ee8b9d789f9be0bab77b765dbda7bc1e8f4dee4fa6ebbc97c7b73755eb7b1d7f70ed0ecb7], [0x70d5c8b5b04b4e2e2717538b9c64af338f6127bda9964acb1b248ced0ea9c49ce2f3a179], []]
  | 5 => [[0x1f], [0x13f6bfafeef89d3be75cbfbbf0ae3fc97edf23e97c3dcdf93e5ec3f85fb7e2fc4fb3f05f3ff4fdffc7e0fc6f8be], [], []]
  | 6 => [[0x1f], [], [], []]
  | _ => []

def C6_S (s j : Nat) : List Nat :=
  qGroupedState C6_initial 4 32 6 C6_patterns C6_values (C6_counts s) (C6_specs s) (C6_records s) j

def C6_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C6_initial (C6_counts s) (C6_specs s) (C6_seeds s) ws
