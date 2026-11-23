def C2_initial : List Nat := [0x1e40, 0x2295, 0x252a, 0x41cc, 0x4833, 0x81f0, 0x900f]

def C2_values : Nat := 0xdff0de40d83fd833d80fd800d00fd000c9f3c9f0c833c1fcc1f0c000b52ab29fb295b00fa52aa295a1f09ff09e4f9e40980f920f91f0900089f083f080006ab7652a63dd5fcc5e735e4049ff480041c040844040400c40003ed53e402d2a27bf272a220020000800020001c000840040000c00050003

def C2_patterns : Nat := 0x0

def C2_N : Nat → Nat
  | 4 => 2
  | 5 => 10
  | 6 => 25
  | 7 => 41
  | 8 => 27
  | 9 => 1
  | _ => 0

def C2_counts : Nat → Nat
  | 4 => 0x1001000
  | 5 => 0x1007002000
  | 6 => 0x1015003000
  | 7 => 0xd01b001
  | 8 => 0x16005
  | 9 => 1
  | _ => 0

def C2_specs : Nat → Nat
  | 4 => 0x101101000
  | 5 => 0x101481181000
  | 6 => 0x101401201000
  | 7 => 0x581501101
  | 8 => 0x501282
  | 9 => 257
  | _ => 0

def C2_seeds : Nat → List Nat
  | 4 => [0x0, 0x2, 0x2, 0x0]
  | 5 => [0x0, 0x1, 0x11a02, 0x2]
  | 6 => [0x0, 0x4, 0x2d940d499202, 0x2]
  | 7 => [0x2, 0x1272c1b0455e00445, 0x60a4d000807, 0x0]
  | 8 => [0x161, 0x14084d4016e017, 0x0, 0x0]
  | 9 => [0x2, 0x0, 0x0, 0x0]
  | _ => []

def C2_records : Nat → List (List Nat)
  | 4 => [[], [0x1b07], [0x75c86], []]
  | 5 => [[], [0x3aada17], [0x16c86a456340a87b6b33c483b7c83f3707], [0x1cc8806]]
  | 6 => [[], [0x407e4bd757], [0x76bd638cf30205d0371c6827bd7adcc87b8807ccbd6d6f2f92b1e442b5921ea68b2719e2d80de324e9203d6487e992d4cac7], [0x1cba807]]
  | 7 => [[0x7f], [0x54fd3ef0df5ff15f4eff7df7efbd7d0ef1bf9ef9bee4bea7789f97ed1eedfb4bbc07e0bf25e577cd7f57e77e], [0x388675d0edaa0ddd42bcd2de408ceda1cef42bcc857999ae613e6680ff2867], []]
  | 8 => [[0x155656555595955555], [0x18ff87f0bf93fc5fe87fcff89fc6fe47f33f87fdafeb7f43bf3fdcfecff3ff83fe6be3ff], [], []]
  | 9 => [[0x7f], [], [], []]
  | _ => []

def C2_S (s j : Nat) : List Nat :=
  qGroupedState C2_initial 4 16 6 C2_patterns C2_values (C2_counts s) (C2_specs s) (C2_records s) j

def C2_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C2_initial (C2_counts s) (C2_specs s) (C2_seeds s) ws
