def C16_initial : List Nat := [0x235, 0x3ca, 0x4a4, 0xc51, 0x1105, 0x2806, 0x3038]

def C16_values : Nat := 0xf1e7907e0fb838e01b4bcd0e33fac8f7238c4f7138c4170b8c1e3000b29ac57b146c06af3aa37a81a906a21a846a0024a48f2a2358001f757555c5164157b5569550552913cf4f293854d153354c15235461514544010003f6cf513bd4ed139d4e513544cf53344ca42f28a3520007ee1f287a41b906b51a9063516904e412004000ffc3350c002b50a002750900230089021108142040800100020004000c00240080011004000800140040008001

def C16_N : Nat → Nat
  | 6 => 24
  | 7 => 78
  | 8 => 51
  | 9 => 1
  | _ => 0

def C16_countBits : Nat → Nat
  | 6 => 1
  | 7 => 1
  | 8 => 2
  | 9 => 1
  | _ => 0

def C16_slots : Nat → Nat
  | 6 => 2
  | 7 => 2
  | 8 => 1
  | _ => 0

def C16_recordBits : Nat → Nat
  | 6 => 21
  | 7 => 21
  | 8 => 21
  | 9 => 7
  | _ => 0

def C16_records : Nat → List Nat
  | 6 => [0xb681d4e5b5adad6c016f6708350077b9221f0017f6c0e672d41c8031ec0117a78e760041e9c2dcd3905a008fd5b70b803add55cae9ce275b9c7a8a1b401c6e]
  | 7 => [0x20fc023fe0159fce1d78017fc84dfa0136fbd73b8010fc01aef00db7801df80557e00e7b00abb8023f8020f402c6f5a3bb0031f804ebe010fe0053f0085bc052eec9776004bf6373b8034de024fb00b7f001ff8043ee00b7e0057f3967b801ffc013fe00bbf00c17c02cee030bf00fbd808bf8037fc01c6f00a3edb1cf803cfa0265f0107f00977d2a1f401cfea887d0049f405e7e0255f00b7b201de803fde02dbf0146f805bdc013fc00efb00c3f00aefc038dc01c7e0123e8041ec019fc00f7b00a7d80b2fdc0edc0007f]
  | 8 => [0x5d555572aa91155504aaadf5555caaaae555400aca80559432aab91555a0aaaae555532aaa855547aaaad4555712aaa2155556aaa8095541aaaa0195512aaada555402cab7155502aaa8a555472aa86d55534aaac0555402aad3d555c6aaab3555462aaa0155916aaa85555422aaa355554aaaa87555592aaa8555500aaac655569aaaa39555]
  | 9 => [0x7f]
  | _ => []

def C16_buckets : Nat → Nat
  | 6 => 6
  | 7 => 20
  | 8 => 13
  | 9 => 1
  | _ => 0

def C16_flag : Nat → Nat
  | 6 => 0x1000
  | 7 => 0x800
  | 8 => 0x800
  | 9 => 2
  | _ => 0

def C16_seedBits : Nat → Nat
  | 6 => 13
  | 7 => 12
  | 8 => 12
  | 9 => 2
  | _ => 0

def C16_seeds : Nat → Nat
  | 6 => 0x1e420228048104002007
  | 7 => 0x7d435901884984e0d500300507c01000100f00300100180005309f017007
  | 8 => 0x63900607501300925609301800100900f82b023
  | 9 => 2
  | _ => 0

def C16_S (s j : Nat) : List Nat :=
  qDirectState C16_initial (C16_countBits s) 14 7 (C16_slots s) C16_values
    (fld ((C16_records s).getD (j / 256) 0) (C16_recordBits s) (j % 256))

def C16_idx : Nat → List Nat → Nat :=
  qIndex C16_N C16_buckets C16_flag C16_seedBits C16_seeds
