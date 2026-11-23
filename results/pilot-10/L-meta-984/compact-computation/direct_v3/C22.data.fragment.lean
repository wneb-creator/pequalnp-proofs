def C22_initial : List Nat := [0x1d1, 0x2a4, 0x64a, 0x928, 0x1430, 0x2038, 0x3807]

def C22_values : Nat := 0x3d38f0dfc30f01faa7e75f92fe41f887e11f83fe003438d0c2938a4a2838a00264a8af22a487e61d184e20b881e202880820088001d3870c16b4592963057c553052c14703da8e4a2eb0aa427e490020007db1d286ca0fd43a40b902800400080010002800800080010001

def C22_N : Nat → Nat
  | 6 => 12
  | 7 => 41
  | 8 => 31
  | 9 => 1
  | _ => 0

def C22_countBits : Nat → Nat
  | 6 => 1
  | 7 => 1
  | 8 => 2
  | 9 => 1
  | _ => 0

def C22_slots : Nat → Nat
  | 6 => 2
  | 7 => 2
  | 8 => 1
  | _ => 0

def C22_recordBits : Nat → Nat
  | 6 => 19
  | 7 => 19
  | 8 => 20
  | 9 => 7
  | _ => 0

def C22_records : Nat → List Nat
  | 6 => [0xae9b20773eb9ed61747c299b797540c27de753c2b97d623c0c8fdd5d3]
  | 7 => [0x165f000fe013f407b78184f0347f5c16c067780defc209e06afc0d9fd305d025be057efcc6780bef029fa023dc092f8077bbc8ae027f716a781edf023be0437c073d8057d018de04d7c0bef8115f020be01bec0baf805fdc5d9e061bc057d816df]
  | 8 => [0x1955a95551d55509555115551555541555a155559555e1555515550555581555bd5550d5553d55581155bd1552155519555dd55549555015593155501555cd55501556025557d555e555501595]
  | 9 => [0x7f]
  | _ => []

def C22_buckets : Nat → Nat
  | 6 => 3
  | 7 => 11
  | 8 => 8
  | 9 => 1
  | _ => 0

def C22_flag : Nat → Nat
  | 6 => 512
  | 7 => 0x400
  | 8 => 0x800
  | 9 => 2
  | _ => 0

def C22_seedBits : Nat → Nat
  | 6 => 10
  | 7 => 11
  | 8 => 12
  | 9 => 2
  | _ => 0

def C22_seeds : Nat → Nat
  | 6 => 0x74b043
  | 7 => 0x1002001422d8c0a0030080a41300c
  | 8 => 0x5da80181f1080ad0bb003002
  | 9 => 2
  | _ => 0

def C22_S (s j : Nat) : List Nat :=
  qDirectState C22_initial (C22_countBits s) 14 6 (C22_slots s) C22_values
    (fld ((C22_records s).getD (j / 256) 0) (C22_recordBits s) (j % 256))

def C22_idx : Nat → List Nat → Nat :=
  qIndex C22_N C22_buckets C22_flag C22_seedBits C22_seeds
