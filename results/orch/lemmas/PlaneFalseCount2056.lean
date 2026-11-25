import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2056_aux.PlaneFalse

def edges : List (Fin 26 × Fin 26) := [
  (0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25),
  (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24),
  (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24),
  (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22),
  (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20),
  (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24),
  (12, 14), (12, 15), (12, 17), (12, 23)
]

def maskEval (m : Nat) : Bool :=
  edges.any fun e => m.testBit e.1.val && m.testBit e.2.val

def maskGood (m : Nat) : Bool :=
  !maskEval m && (List.range 26).all (fun i => m.testBit i || maskEval (m ||| 2 ^ i))

def block0 : List Nat := [
  8191, 15860, 20218, 27888, 34685, 42356, 50808, 58480,
  70590, 78260, 82618, 90288, 99132, 106804, 115256, 133599,
  141780, 149722, 157904, 164189, 172372, 180312, 197022, 205204,
  213146, 229660, 237844, 267503, 275684, 279786, 287968, 296045
]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem checked0 : block0.all maskGood = true := by decide +kernel

def block1 : List Nat := [
  304228, 312424, 320608, 331950, 340132, 344234, 360492, 393423,
  401604, 409802, 426061, 458894, 475274, 531063, 538740, 543346,
  551024, 557685, 565364, 574064, 581744, 594486, 602164, 606770,
  623156, 630836, 639536, 657495, 665684, 673874, 682064, 688213
]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem checked1 : block1.all maskGood = true := by decide +kernel

def block2 : List Nat := [
  696404, 720918, 790631, 798820, 802914, 819301, 827492, 856102,
  864292, 917575, 950341, 1056059, 1064240, 1068090, 1076272, 1082681,
  1090864, 1098808, 1106992, 1118522, 1126704, 1130554, 1147192, 1155376,
  1163320, 1181979, 1190160, 1198106, 1212697, 1245466, 1261594, 1278232
]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem checked2 : block2.all maskGood = true := by decide +kernel

def block3 : List Nat := [
  1315883, 1324064, 1328170, 1344553, 1360936, 1380394, 1392682, 1441803,
  1579059, 1587248, 1591346, 1599536, 1605681, 1642546, 1650736, 1654834,
  1695792, 1706003, 1722386, 1839139, 1904674, 2104989, 2112660, 2117272,
  2124944, 2131485, 2139156, 2147864, 2167452, 2175124, 2179736, 2195996
]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem checked3 : block3.all maskGood = true := by decide +kernel

def block4 : List Nat := [
  2212376, 2230429, 2238612, 2246808, 2254992, 2261021, 2293916, 2302100,
  2310296, 2326556, 2364557, 2372740, 2376840, 2393101, 2429068, 2437252,
  2490509, 2523149, 2556044, 2628117, 2635796, 2640400, 2654741, 2691604,
  2699284, 2720276, 2754581, 2762772, 2785301, 2859028, 2887685, 3152921
]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem checked4 : block4.all maskGood = true := by decide +kernel

def block5 : List Nat := [
  3161104, 3165208, 3173392, 3179545, 3195928, 3215384, 3278873, 3295256,
  3309593, 3391512, 3413001, 3441673, 3676177, 3684368, 3803153, 3827728,
  4202318, 4209988, 4214346, 4222016, 4228940, 4236612, 4245064, 4264718,
  4272388, 4276746, 4293388, 4327758, 4335940, 4343882, 4358476, 4366660
]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem checked5 : block5.all maskGood = true := by decide +kernel

def block6 : List Nat := [
  4391182, 4423948, 4461646, 4469828, 4473930, 4490316, 4498500, 4506696,
  4526094, 4587598, 4603978, 4620364, 4653070, 4725318, 4732996, 4737602,
  4751940, 4788742, 4851782, 4859972, 4868162, 4984902, 4993092, 5050374,
  5111878, 5152836, 5250314, 5258496, 5262346, 5276936, 5312778, 5376266
]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem checked6 : block6.all maskGood = true := by decide +kernel

def block7 : List Nat := [
  5392394, 5439754, 5510154, 5522442, 5574666, 5718026, 5773314, 6299148,
  6306820, 6311432, 6325772, 6342152, 6361612, 6390284, 6424588, 6558732,
  6566916, 6587404, 6623244, 6782988, 6822404, 6830084, 6885892, 7155716,
  7347208, 7355392, 7359496, 7607304, 7652360, 8392615, 8400292, 8408738
]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem checked7 : block7.all maskGood = true := by decide +kernel

def block8 : List Nat := [
  8416416, 8423205, 8430884, 8439328, 8455078, 8462756, 8471202, 8487716,
  8495396, 8522119, 8530308, 8538242, 8552709, 8585606, 8593796, 8651943,
  8660132, 8668322, 8676512, 8684581, 8692772, 8716454, 8724644, 8732834,
  8781959, 8847494, 8915495, 8923172, 8931874, 8946213, 8978982, 8995362
]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem checked8 : block8.all maskGood = true := by decide +kernel

def block9 : List Nat := [
  9011748, 9046023, 9175079, 9207845, 9240614, 9281572, 9306119, 9440547,
  9448736, 9456674, 9464864, 9471265, 9479456, 9503010, 9570563, 9700387,
  9716770, 9733153, 9757728, 9963555, 9979938, 10094595, 10223651, 10305570,
  10489477, 10497156, 10505856, 10513536, 10520069, 10551940, 10619013, 10627204
]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem checked9 : block9.all maskGood = true := by decide +kernel

def block10 : List Nat := [
  10749061, 10757252, 10781701, 10879109, 10952836, 11012613, 11043333, 11143173,
  11436037, 11537409, 12586758, 12594436, 12602882, 12617476, 12625156, 12649222,
  12681988, 12716294, 12724484, 12779782, 12820740, 12846086, 13109766, 13126146,
  13173254, 13240326, 13565958, 13634818, 13643008, 13650946, 13764866, 14305282
]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem checked10 : block10.all maskGood = true := by decide +kernel

def block11 : List Nat := [
  14683652, 14691332, 14700032, 14714372, 14984196, 15206916, 15303172, 15345668,
  15704068, 15756288, 16783315, 16790992, 16795346, 16803024, 16811857, 16819536,
  16827984, 16835664, 16847762, 16855440, 16859794, 16876304, 16908755, 16916944,
  16924882, 16933072, 16941393, 16949584, 16974226, 16982416, 16990354, 17044675
]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem checked11 : block11.all maskGood = true := by decide +kernel

def block12 : List Nat := [
  17052864, 17056962, 17065152, 17073217, 17109122, 17170627, 17187010, 17306195,
  17313872, 17318482, 17334865, 17351248, 17371666, 17383954, 17432659, 17449042,
  17465425, 17490000, 17567811, 17694787, 17831187, 17839376, 17843218, 17859857,
  17868048, 17895698, 17903888, 17957139, 17989905, 18022674, 18063632, 18093059
]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem checked12 : block12.all maskGood = true := by decide +kernel

def block13 : List Nat := [
  18354195, 18419730, 18481171, 18563090, 18616323, 18880145, 18887824, 18892432,
  18900112, 18908689, 18925072, 18944656, 18952336, 18956944, 19005585, 19095696,
  19141761, 19149952, 19403281, 19431953, 19468816, 19513872, 19928081, 19936272,
  19956753, 19981328, 20190209, 20451345, 20525072, 20611089, 20701200, 20977474
]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem checked13 : block13.all maskGood = true := by decide +kernel

def block14 : List Nat := [
  20985152, 20989506, 21006144, 21013824, 21022272, 21041922, 21102914, 21238850,
  21247040, 21251138, 21292096, 21500482, 21512770, 21565954, 21762114, 21905474,
  22025474, 22033664, 22089986, 22287362, 22876162, 23074304, 24392704, 25167747,
  25175424, 25183874, 25200385, 25232258, 25248386, 25297283, 25362818, 25429123
]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem checked14 : block14.all maskGood = true := by decide +kernel

def block15 : List Nat := [
  25445506, 25559171, 25641090, 25690627, 26215683, 26248449, 26345731, 26477571,
  27131907, 27264641, 27281024, 27297281, 27526273, 27550848, 28607489, 29361922,
  29378050, 29394688, 29426434, 29966850, 30409986, 30450944, 30605570, 30688258,
  31408130, 31507968, 32826368, 33561577, 33569248, 33573608, 33581280, 33588073
]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem checked15 : block15.all maskGood = true := by decide +kernel

def block16 : List Nat := [
  33595744
]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem checked16 : block16.all maskGood = true := by decide +kernel

def masks : List Nat :=
  block0 ++ block1 ++ block2 ++ block3 ++ block4 ++ block5 ++ block6 ++ block7 ++ block8 ++ block9 ++ block10 ++ block11 ++ block12 ++ block13 ++ block14 ++ block15 ++ block16

theorem masks_length : masks.length = 513 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem masks_nodup : masks.Nodup := by decide +kernel

theorem masks_good : masks.all maskGood = true := by
  simp only [masks, List.all_append, checked0, checked1, checked2, checked3, checked4, checked5, checked6, checked7, checked8, checked9, checked10, checked11, checked12, checked13, checked14, checked15, checked16]
  rfl

set_option maxRecDepth 10000 in
theorem masks_bound : masks.all (fun m => decide (m < 2 ^ 26)) = true := by decide +kernel

end PEqualNP.Outside.L_meta_2056_aux.PlaneFalse
