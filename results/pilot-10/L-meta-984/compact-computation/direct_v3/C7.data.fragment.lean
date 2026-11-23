def C7_initial : List Nat := [0x750, 0x98d, 0x122b, 0x20f8, 0x2407, 0x4832, 0x50c4]

def C7_values : Nat := 0xe989c31361bec32d1f5a0cb203e0f8b39b63dac6254c4a58948ae8e24f72937f20023a840006c56c8ad6c7ac0753faa3e13fc27574ea0941d27fa4f8480087e1028203040508000dd79a2b2c564cac7ee8f5012002000200010000a000c00140022002000240018002

def C7_N : Nat → Nat
  | 5 => 3
  | 6 => 11
  | 7 => 40
  | 8 => 34
  | 9 => 1
  | _ => 0

def C7_countBits : Nat → Nat
  | 5 => 1
  | 6 => 1
  | 7 => 1
  | 8 => 2
  | 9 => 1
  | _ => 0

def C7_slots : Nat → Nat
  | 5 => 2
  | 6 => 2
  | 7 => 2
  | 8 => 1
  | _ => 0

def C7_recordBits : Nat → Nat
  | 5 => 19
  | 6 => 19
  | 7 => 19
  | 8 => 20
  | 9 => 7
  | _ => 0

def C7_records : Nat → List Nat
  | 5 => [0x12398b8911f1a87]
  | 6 => [0x9a18e373900c67df32f2318f771b44e66de367c309dc63300e76]
  | 7 => [0x16ee054fc09ef80af7010f6033dc04fb80c6f014ee043bd32b380e760377e03fdc037f0067d8d3e603ddc0cb7808fb02c7e039fa24f3818f779dec001fc0b9f80c77798cee27d8073b80c67dd36e04df806f7815fb023f601fec0b5f80bf7]
  | 8 => [0x15954d51525555016550555581555a5555695552d5550d5554d55579515395559555579555a155511555bd55501556d95552155549555c1555015551955515555d15558955529555095551d555019557555501559]
  | 9 => [0x7f]
  | _ => []

def C7_buckets : Nat → Nat
  | 5 => 1
  | 6 => 3
  | 7 => 10
  | 8 => 9
  | 9 => 1
  | _ => 0

def C7_flag : Nat → Nat
  | 5 => 8
  | 6 => 32
  | 7 => 0x400
  | 8 => 0x1000
  | 9 => 2
  | _ => 0

def C7_seedBits : Nat → Nat
  | 5 => 4
  | 6 => 6
  | 7 => 11
  | 8 => 13
  | 9 => 2
  | _ => 0

def C7_seeds : Nat → Nat
  | 5 => 7
  | 6 => 0x18093
  | 7 => 0xb860340dd0020950dc0201500f
  | 8 => 0x1015750000c4d102281103040080a2
  | 9 => 2
  | _ => 0

def C7_S (s j : Nat) : List Nat :=
  qDirectState C7_initial (C7_countBits s) 15 6 (C7_slots s) C7_values
    (fld ((C7_records s).getD (j / 256) 0) (C7_recordBits s) (j % 256))

def C7_idx : Nat → List Nat → Nat :=
  qIndex C7_N C7_buckets C7_flag C7_seedBits C7_seeds
