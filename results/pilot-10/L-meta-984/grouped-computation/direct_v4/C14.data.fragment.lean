def C14_initial : List Nat := [0x1e8, 0x252, 0x41a, 0x625, 0x914, 0x101c, 0x1883]

def C14_values : Nat := 0x1ea7e41ea0f3f99ebcf4665f329983c8e64531878a3c40607300163db12d7f2bd141ea0e506a80125290e47f23d111c84e42020b903c8003cd5a3cd145ab2c5132895449a1fb4e4a67732d1948c7e5fa2f4106082441020410088003fa1f40d4848020002000800300120080020004001

def C14_patterns : Nat := 0x0

def C14_N : Nat → Nat
  | 5 => 4
  | 6 => 27
  | 7 => 53
  | 8 => 30
  | 9 => 1
  | _ => 0

def C14_counts : Nat → Nat
  | 5 => 0x3001000
  | 6 => 0x1014006000
  | 7 => 0x10024001
  | 8 => 0x19005
  | 9 => 1
  | _ => 0

def C14_specs : Nat → Nat
  | 5 => 0x201101000
  | 6 => 0x101581401000
  | 7 => 0x481481101
  | 8 => 0x401282
  | 9 => 257
  | _ => 0

def C14_seeds : Nat → List Nat
  | 5 => [0x0, 0x2, 0x4, 0x0]
  | 6 => [0x0, 0x8549, 0x20062260a3dc, 0x2]
  | 7 => [0x2, 0x9303c75f626030440236, 0xd005ce1f, 0x0]
  | 8 => [0x101, 0x12150a0794846a, 0x0, 0x0]
  | 9 => [0x2, 0x0, 0x0, 0x0]
  | _ => []

def C14_records : Nat → List (List Nat)
  | 5 => [[], [0x195a], [0x407e39d9792eca4a], []]
  | 6 => [[], [0x8179c1f773df4f5d6d55e], [0x6052d2129a9e0b9aec74b76be5b32969daa9d110ab76565bb5b3550eb51181b76d23bb312de1a8efdb0f68aab3d783de14b4aca5a], [0x7880c49]]
  | 7 => [[0x7f], [0x86fe15f3bbce6f4d7d5df5579e5f1dedb5f77bc87b6f7debf597ddcf777c9fb617d2df29f9d3f23ed0ef15f467e557cf6f517d3df3fbc7fb72fc97b537e23f], [0x76927bc473e0abbcfde4f563adc41cede0eb65077a7862dbc413de15b69075b423b5b01d6d595b660479], []]
  | 8 => [[0x155556555595595556], [0xff797c1ff1bfd17f2bfe2ff2dfd5df63fd1ff05fdaff31fc4ff0ffc27f1dec2ff1dfcdff41fccff11fc37f], [], []]
  | 9 => [[0x7f], [], [], []]
  | _ => []

def C14_S (s j : Nat) : List Nat :=
  qGroupedState C14_initial 4 13 7 C14_patterns C14_values (C14_counts s) (C14_specs s) (C14_records s) j

def C14_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C14_initial (C14_counts s) (C14_specs s) (C14_seeds s) ws
