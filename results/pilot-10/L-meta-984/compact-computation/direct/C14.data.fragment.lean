def C14_initial : List Nat := [0x1e8, 0x252, 0x41a, 0x625, 0x914, 0x101c, 0x1883]

def C14_values : Nat := 0x1ea7e41ea0f3f99ebcf4665f329983c8e64531878a3c40607300163db12d7f2bd141ea0e506a80125290e47f23d111c84e42020b903c8003cd5a3cd145ab2c5132895449a1fb4e4a67732d1948c7e5fa2f4106082441020410088003fa1f40d4848020002000800300120080020004001

def C14_N : Nat → Nat
  | 5 => 4
  | 6 => 27
  | 7 => 53
  | 8 => 30
  | 9 => 1
  | _ => 0

def C14_countBits : Nat → Nat
  | 5 => 1
  | 6 => 1
  | 7 => 1
  | 8 => 2
  | 9 => 1
  | _ => 0

def C14_slots : Nat → Nat
  | 5 => 2
  | 6 => 3
  | 7 => 2
  | 8 => 1
  | _ => 0

def C14_recordBits : Nat → Nat
  | 5 => 21
  | 6 => 28
  | 7 => 21
  | 8 => 21
  | 9 => 7
  | _ => 0

def C14_records : Nat → Nat
  | 5 => 0x765e4c07e38032b4eca4a
  | 6 => 0xecacb00ec74b00f5e0f00f0a5a00d15560084a6a0001dcf00fdb0f011181b00ed6cd0001c1f00f0d47000205e7880c4900cca5a00aca5a000175b00eda4700ed54e00a875a00c0a5a00f05cd01110ab000155e00ed7cb0001f4f00ecc4b
  | 7 => 0x13df009af806f7c00afa01cbf00ef78088fc030be0067e003bd8021ec03cbe0007f00777bc2b6cc08f2fde4f004bdbc1d6c03d7ef104f007b7806d7d595b600a7e0096f80597d80eb65077a00aaf8039bc021de008fb010dfa41d6d08ed6007fb00e9f8027ed58eb60145f00eef80857e0abbc014df00aaf3b493de18b601dcf00aefbc473c01fdf1073b
  | 8 => 0xaaaa355550caaa9655544aaaaad15530aaa83555472aaa8155504aaa80556472a8af115500ab2b15554daaaa6555500acaa255562aaaa2155546aaa955555aaaaa1555508aaa8055583aaaa01555
  | 9 => 127
  | _ => 0

def C14_buckets : Nat → Nat
  | 5 => 1
  | 6 => 7
  | 7 => 14
  | 8 => 8
  | 9 => 1
  | _ => 0

def C14_flag : Nat → Nat
  | 5 => 32
  | 6 => 512
  | 7 => 512
  | 8 => 256
  | 9 => 2
  | _ => 0

def C14_seedBits : Nat → Nat
  | 5 => 6
  | 6 => 10
  | 7 => 10
  | 8 => 9
  | 9 => 2
  | _ => 0

def C14_seeds : Nat → Nat
  | 5 => 18
  | 6 => 0x101c0b3fe1383550
  | 7 => 0x801856116760a060e90104302c2102444
  | 8 => 0xe47405100080c36ba
  | 9 => 2
  | _ => 0

def C14_S (s j : Nat) : List Nat :=
  qDirectState C14_initial (C14_countBits s) 13 7 (C14_slots s) C14_values
    (fld (C14_records s) (C14_recordBits s) j)

def C14_idx : Nat → List Nat → Nat :=
  qIndex C14_N C14_buckets C14_flag C14_seedBits C14_seeds
