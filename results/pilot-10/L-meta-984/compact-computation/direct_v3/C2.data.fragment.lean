def C2_initial : List Nat := [0x1e40, 0x2295, 0x252a, 0x41cc, 0x4833, 0x81f0, 0x900f]

def C2_values : Nat := 0xdff0de40d83fd833d80fd800d00fd000c9f3c9f0c833c1fcc1f0c000b52ab29fb295b00fa52aa295a1f09ff09e4f9e40980f920f91f0900089f083f080006ab7652a63dd5fcc5e735e4049ff480041c040844040400c40003ed53e402d2a27bf272a220020000800020001c000840040000c00050003

def C2_N : Nat → Nat
  | 4 => 2
  | 5 => 10
  | 6 => 25
  | 7 => 41
  | 8 => 27
  | 9 => 1
  | _ => 0

def C2_countBits : Nat → Nat
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | 7 => 1
  | 8 => 2
  | 9 => 1
  | _ => 0

def C2_slots : Nat → Nat
  | 4 => 2
  | 5 => 3
  | 6 => 3
  | 7 => 2
  | 8 => 1
  | _ => 0

def C2_recordBits : Nat → Nat
  | 4 => 19
  | 5 => 25
  | 6 => 25
  | 7 => 19
  | 8 => 20
  | 9 => 7
  | _ => 0

def C2_records : Nat → List Nat
  | 4 => [0xd83f5c86]
  | 5 => [0xe241c040a8702456300075580df20e05b21a000d0b81cdc1c0b6b33cc8806]
  | 6 => [0x76bd602c90f000407c0997adcba8070234138132b1c0024bc01c67900e33c0081b8c09203c001757035bcb81c403c0a64b4064ac702040b814d1640910ac05921f02f5eb016c06c0c649c07321e]
  | 7 => [0x77fbd0ae8119db4398125f00afa01bec086f811bf020be06afc0bef80dfb710ce01dfb94338113f014ee023dc05ff0097701fbe0407c04fb8135f000fe03d7cc27c80aef9a5bdaa0dc09efae876024bc021ddd42bcc857999ae054fe680f805fb]
  | 8 => [0x4155509555015562555569555cd5553d55505555315551955571555e55551d5550159501559655551555521555c15551155541515991550d55561555595550155501655]
  | 9 => [0x7f]
  | _ => []

def C2_buckets : Nat → Nat
  | 4 => 1
  | 5 => 3
  | 6 => 7
  | 7 => 11
  | 8 => 7
  | 9 => 1
  | _ => 0

def C2_flag : Nat → Nat
  | 4 => 4
  | 5 => 256
  | 6 => 256
  | 7 => 0x400
  | 8 => 0x2000
  | 9 => 2
  | _ => 0

def C2_seedBits : Nat → Nat
  | 4 => 3
  | 5 => 9
  | 6 => 9
  | 7 => 11
  | 8 => 14
  | 9 => 2
  | _ => 0

def C2_seeds : Nat → Nat
  | 4 => 2
  | 5 => 0x9bf0a
  | 6 => 0x62a020481c06fd
  | 7 => 0x8420084c0080480600100871c05866
  | 8 => 0x116e03fc0240038003000c001
  | 9 => 2
  | _ => 0

def C2_S (s j : Nat) : List Nat :=
  qDirectState C2_initial (C2_countBits s) 16 6 (C2_slots s) C2_values
    (fld ((C2_records s).getD (j / 256) 0) (C2_recordBits s) (j % 256))

def C2_idx : Nat → List Nat → Nat :=
  qIndex C2_N C2_buckets C2_flag C2_seedBits C2_seeds
