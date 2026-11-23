def C4_initial : List Nat := [0x721, 0x94a, 0xa94, 0x20e7, 0x3418, 0x40f8, 0x5007]

def C4_values : Nat := 0xefcfdc87a7c741fe831d01fa0070e7e1c1c01f80060ffc1f1839f0005a94b29f652ac03d727ae43501e883d0ffa1f1400254a49fa929523e23fcc72189f107e20704048804100620003d5a7830dce5b90b51869fed001873b0005528a7bd4a528e74fce9c85273a40043ce83810212021400e8000d4a172120003dac7908e9417bc2e5048008000800040007000480084008401000180010001c0010001

def C4_patterns : Nat := 0x0

def C4_N : Nat → Nat
  | 4 => 2
  | 5 => 18
  | 6 => 51
  | 7 => 79
  | 8 => 44
  | 9 => 1
  | _ => 0

def C4_counts : Nat → Nat
  | 4 => 0x1001000
  | 5 => 0x400d001000
  | 6 => 0x4026009000
  | 7 => 0x1a034001
  | 8 => 0x25007
  | 9 => 1
  | _ => 0

def C4_specs : Nat → Nat
  | 4 => 0x101101000
  | 5 => 0x301301101000
  | 6 => 0x201581401000
  | 7 => 0x601501101
  | 8 => 0x481302
  | 9 => 257
  | _ => 0

def C4_seeds : Nat → List Nat
  | 4 => [0x0, 0x2, 0x2, 0x0]
  | 5 => [0x0, 0x2, 0xb5504e, 0x10]
  | 6 => [0x0, 0x887802, 0x2130150220108027100eb7824819, 0x1]
  | 7 => [0x2, 0x3d78a2f0f1e706c0116c6a01c0400442, 0x81a07e027004001402014, 0x0]
  | 8 => [0x4c3, 0x18e0f0d0044c3392a980433, 0x0, 0x0]
  | 9 => [0x2, 0x0, 0x0, 0x0]
  | _ => []

def C4_records : Nat → List (List Nat)
  | 4 => [[], [0x2707], [0x14e806], []]
  | 5 => [[], [0x2517], [0x140fc6a9403bb3a1e84a0f4200e8b00d2e545a84d0f42587767cb529e1d7270f16199], [0x9ae9a929ae9c11a135a86a135d03]]
  | 6 => [[], [0x2357a13d576995cff696ddd9f4f9e7b7], [0x1d35b4e9c59a11e3d23b1d222e340bc78aecdbb405e84d4f2d2335c94bd09b1d21fe542697907eb50823d7262f426879aecbbb365e91fad2cfb6a0ea5c0767aa2e2f4104796b8bcd5e5e6ae2f41ace9720bae3f5a84d1eb8a9e2443c52965dd972f41d8f], [0x9ad57169ae9713a135707a546687]]
  | 7 => [[0x7f], [0x4dde85f7efdbdf917cd77777d85f49ed4efa1bda5fa9ddafe41dd8df3bdddbf677e5f72bfa95f5f7de5f9bdd95f767d66f3fde3f723ecf773fda5bf96dc7fb4bdcc7733de84f37ddf3f2decffe25f877d39dd75f75ecbf743de13f], [0xf97ed48dd7a5467d05d3dd2eb73571f9ababcb2edd5a0ed357376abaf529b5d217e71d7572037cd19add720aeb8bd75c50fc15c7e6b2af48bd79ab8bc82f5e93b3f49057], []]
  | 8 => [[0x2555555559559555596555556], [0x17f1bfe6f7a5fc1ffa57d0777bfc47f29fe6ff47fc87f83fc0ff89fc9ff17fe8ff93fdb7f13fc37f41fd5ff15fcbf75dfd6ff73fc3ff5d7d47f2ffc27f0bfc67f], [], []]
  | 9 => [[0x7f], [], [], []]
  | _ => []

def C4_S (s j : Nat) : List Nat :=
  qGroupedState C4_initial 4 15 7 C4_patterns C4_values (C4_counts s) (C4_specs s) (C4_records s) j

def C4_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C4_initial (C4_counts s) (C4_specs s) (C4_seeds s) ws
