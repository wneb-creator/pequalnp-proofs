; benchmark generated from python API
(set-info :status unknown)
(declare-fun left_0_5 () Bool)
(declare-fun left_0_4 () Bool)
(declare-fun left_0_3 () Bool)
(declare-fun left_0_2 () Bool)
(declare-fun left_0_1 () Bool)
(declare-fun left_0_0 () Bool)
(declare-fun right_0_5 () Bool)
(declare-fun right_0_4 () Bool)
(declare-fun right_0_3 () Bool)
(declare-fun right_0_2 () Bool)
(declare-fun right_0_1 () Bool)
(declare-fun right_0_0 () Bool)
(declare-fun is_or_0 () Bool)
(declare-fun function_0 () (_ BitVec 64))
(declare-fun left_1_6 () Bool)
(declare-fun left_1_5 () Bool)
(declare-fun left_1_4 () Bool)
(declare-fun left_1_3 () Bool)
(declare-fun left_1_2 () Bool)
(declare-fun left_1_1 () Bool)
(declare-fun left_1_0 () Bool)
(declare-fun right_1_6 () Bool)
(declare-fun right_1_5 () Bool)
(declare-fun right_1_4 () Bool)
(declare-fun right_1_3 () Bool)
(declare-fun right_1_2 () Bool)
(declare-fun right_1_1 () Bool)
(declare-fun right_1_0 () Bool)
(declare-fun is_or_1 () Bool)
(declare-fun function_1 () (_ BitVec 64))
(declare-fun left_2_7 () Bool)
(declare-fun left_2_6 () Bool)
(declare-fun left_2_5 () Bool)
(declare-fun left_2_4 () Bool)
(declare-fun left_2_3 () Bool)
(declare-fun left_2_2 () Bool)
(declare-fun left_2_1 () Bool)
(declare-fun left_2_0 () Bool)
(declare-fun right_2_7 () Bool)
(declare-fun right_2_6 () Bool)
(declare-fun right_2_5 () Bool)
(declare-fun right_2_4 () Bool)
(declare-fun right_2_3 () Bool)
(declare-fun right_2_2 () Bool)
(declare-fun right_2_1 () Bool)
(declare-fun right_2_0 () Bool)
(declare-fun is_or_2 () Bool)
(declare-fun function_2 () (_ BitVec 64))
(declare-fun left_3_8 () Bool)
(declare-fun left_3_7 () Bool)
(declare-fun left_3_6 () Bool)
(declare-fun left_3_5 () Bool)
(declare-fun left_3_4 () Bool)
(declare-fun left_3_3 () Bool)
(declare-fun left_3_2 () Bool)
(declare-fun left_3_1 () Bool)
(declare-fun left_3_0 () Bool)
(declare-fun right_3_8 () Bool)
(declare-fun right_3_7 () Bool)
(declare-fun right_3_6 () Bool)
(declare-fun right_3_5 () Bool)
(declare-fun right_3_4 () Bool)
(declare-fun right_3_3 () Bool)
(declare-fun right_3_2 () Bool)
(declare-fun right_3_1 () Bool)
(declare-fun right_3_0 () Bool)
(declare-fun is_or_3 () Bool)
(declare-fun function_3 () (_ BitVec 64))
(declare-fun left_4_9 () Bool)
(declare-fun left_4_8 () Bool)
(declare-fun left_4_7 () Bool)
(declare-fun left_4_6 () Bool)
(declare-fun left_4_5 () Bool)
(declare-fun left_4_4 () Bool)
(declare-fun left_4_3 () Bool)
(declare-fun left_4_2 () Bool)
(declare-fun left_4_1 () Bool)
(declare-fun left_4_0 () Bool)
(declare-fun right_4_9 () Bool)
(declare-fun right_4_8 () Bool)
(declare-fun right_4_7 () Bool)
(declare-fun right_4_6 () Bool)
(declare-fun right_4_5 () Bool)
(declare-fun right_4_4 () Bool)
(declare-fun right_4_3 () Bool)
(declare-fun right_4_2 () Bool)
(declare-fun right_4_1 () Bool)
(declare-fun right_4_0 () Bool)
(declare-fun is_or_4 () Bool)
(declare-fun function_4 () (_ BitVec 64))
(assert
 ((_ pbeq 1 1 1 1 1 1 1) left_0_0 left_0_1 left_0_2 left_0_3 left_0_4 left_0_5))
(assert
 ((_ pbeq 1 1 1 1 1 1 1) right_0_0 right_0_1 right_0_2 right_0_3 right_0_4 right_0_5))
(assert
 (let (($x44 (not right_0_0)))
 (or (not left_0_0) $x44)))
(assert
 (let (($x44 (not right_0_0)))
 (let (($x46 (not left_0_1)))
 (or $x46 $x44))))
(assert
 (let (($x48 (not right_0_1)))
 (let (($x46 (not left_0_1)))
 (or $x46 $x48))))
(assert
 (let (($x44 (not right_0_0)))
 (let (($x50 (not left_0_2)))
 (or $x50 $x44))))
(assert
 (let (($x48 (not right_0_1)))
 (let (($x50 (not left_0_2)))
 (or $x50 $x48))))
(assert
 (let (($x53 (not right_0_2)))
 (let (($x50 (not left_0_2)))
 (or $x50 $x53))))
(assert
 (let (($x44 (not right_0_0)))
 (let (($x55 (not left_0_3)))
 (or $x55 $x44))))
(assert
 (let (($x48 (not right_0_1)))
 (let (($x55 (not left_0_3)))
 (or $x55 $x48))))
(assert
 (let (($x53 (not right_0_2)))
 (let (($x55 (not left_0_3)))
 (or $x55 $x53))))
(assert
 (let (($x59 (not right_0_3)))
 (let (($x55 (not left_0_3)))
 (or $x55 $x59))))
(assert
 (let (($x44 (not right_0_0)))
 (let (($x61 (not left_0_4)))
 (or $x61 $x44))))
(assert
 (let (($x48 (not right_0_1)))
 (let (($x61 (not left_0_4)))
 (or $x61 $x48))))
(assert
 (let (($x53 (not right_0_2)))
 (let (($x61 (not left_0_4)))
 (or $x61 $x53))))
(assert
 (let (($x59 (not right_0_3)))
 (let (($x61 (not left_0_4)))
 (or $x61 $x59))))
(assert
 (let (($x66 (not right_0_4)))
 (let (($x61 (not left_0_4)))
 (or $x61 $x66))))
(assert
 (let (($x44 (not right_0_0)))
 (let (($x68 (not left_0_5)))
 (or $x68 $x44))))
(assert
 (let (($x48 (not right_0_1)))
 (let (($x68 (not left_0_5)))
 (or $x68 $x48))))
(assert
 (let (($x53 (not right_0_2)))
 (let (($x68 (not left_0_5)))
 (or $x68 $x53))))
(assert
 (let (($x59 (not right_0_3)))
 (let (($x68 (not left_0_5)))
 (or $x68 $x59))))
(assert
 (let (($x66 (not right_0_4)))
 (let (($x68 (not left_0_5)))
 (or $x68 $x66))))
(assert
 (let (($x68 (not left_0_5)))
 (or $x68 (not right_0_5))))
(assert
 (let ((?x99 (ite right_0_5 (_ bv18446744069414584320 64) (_ bv0 64))))
 (let ((?x97 (ite right_0_4 (_ bv18446462603027742720 64) (_ bv0 64))))
 (let ((?x95 (ite right_0_3 (_ bv18374966859414961920 64) (_ bv0 64))))
 (let ((?x93 (ite right_0_2 (_ bv17361641481138401520 64) (_ bv0 64))))
 (let ((?x91 (ite right_0_1 (_ bv14757395258967641292 64) (_ bv0 64))))
 (let ((?x96 (bvor (bvor (bvor (bvor (_ bv0 64) (ite right_0_0 (_ bv12297829382473034410 64) (_ bv0 64))) ?x91) ?x93) ?x95)))
 (let ((?x100 (bvor (bvor ?x96 ?x97) ?x99)))
 (let ((?x87 (ite left_0_5 (_ bv18446744069414584320 64) (_ bv0 64))))
 (let ((?x85 (ite left_0_4 (_ bv18446462603027742720 64) (_ bv0 64))))
 (let ((?x83 (ite left_0_3 (_ bv18374966859414961920 64) (_ bv0 64))))
 (let ((?x81 (ite left_0_2 (_ bv17361641481138401520 64) (_ bv0 64))))
 (let ((?x79 (ite left_0_1 (_ bv14757395258967641292 64) (_ bv0 64))))
 (let ((?x84 (bvor (bvor (bvor (bvor (_ bv0 64) (ite left_0_0 (_ bv12297829382473034410 64) (_ bv0 64))) ?x79) ?x81) ?x83)))
 (let ((?x88 (bvor (bvor ?x84 ?x85) ?x87)))
 (= function_0 (ite is_or_0 (bvor ?x88 ?x100) (bvand ?x88 ?x100))))))))))))))))))
(assert
 (and (distinct (_ bv12297829382473034410 64) function_0) true))
(assert
 (and (distinct (_ bv14757395258967641292 64) function_0) true))
(assert
 (and (distinct (_ bv17361641481138401520 64) function_0) true))
(assert
 (and (distinct (_ bv18374966859414961920 64) function_0) true))
(assert
 (and (distinct (_ bv18446462603027742720 64) function_0) true))
(assert
 (and (distinct (_ bv18446744069414584320 64) function_0) true))
(assert
 ((_ pbeq 1 1 1 1 1 1 1 1) left_1_0 left_1_1 left_1_2 left_1_3 left_1_4 left_1_5 left_1_6))
(assert
 ((_ pbeq 1 1 1 1 1 1 1 1) right_1_0 right_1_1 right_1_2 right_1_3 right_1_4 right_1_5 right_1_6))
(assert
 (let (($x163 (not right_1_0)))
 (or (not left_1_0) $x163)))
(assert
 (let (($x163 (not right_1_0)))
 (let (($x165 (not left_1_1)))
 (or $x165 $x163))))
(assert
 (let (($x167 (not right_1_1)))
 (let (($x165 (not left_1_1)))
 (or $x165 $x167))))
(assert
 (let (($x163 (not right_1_0)))
 (let (($x169 (not left_1_2)))
 (or $x169 $x163))))
(assert
 (let (($x167 (not right_1_1)))
 (let (($x169 (not left_1_2)))
 (or $x169 $x167))))
(assert
 (let (($x172 (not right_1_2)))
 (let (($x169 (not left_1_2)))
 (or $x169 $x172))))
(assert
 (let (($x163 (not right_1_0)))
 (let (($x174 (not left_1_3)))
 (or $x174 $x163))))
(assert
 (let (($x167 (not right_1_1)))
 (let (($x174 (not left_1_3)))
 (or $x174 $x167))))
(assert
 (let (($x172 (not right_1_2)))
 (let (($x174 (not left_1_3)))
 (or $x174 $x172))))
(assert
 (let (($x178 (not right_1_3)))
 (let (($x174 (not left_1_3)))
 (or $x174 $x178))))
(assert
 (let (($x163 (not right_1_0)))
 (let (($x180 (not left_1_4)))
 (or $x180 $x163))))
(assert
 (let (($x167 (not right_1_1)))
 (let (($x180 (not left_1_4)))
 (or $x180 $x167))))
(assert
 (let (($x172 (not right_1_2)))
 (let (($x180 (not left_1_4)))
 (or $x180 $x172))))
(assert
 (let (($x178 (not right_1_3)))
 (let (($x180 (not left_1_4)))
 (or $x180 $x178))))
(assert
 (let (($x185 (not right_1_4)))
 (let (($x180 (not left_1_4)))
 (or $x180 $x185))))
(assert
 (let (($x163 (not right_1_0)))
 (let (($x187 (not left_1_5)))
 (or $x187 $x163))))
(assert
 (let (($x167 (not right_1_1)))
 (let (($x187 (not left_1_5)))
 (or $x187 $x167))))
(assert
 (let (($x172 (not right_1_2)))
 (let (($x187 (not left_1_5)))
 (or $x187 $x172))))
(assert
 (let (($x178 (not right_1_3)))
 (let (($x187 (not left_1_5)))
 (or $x187 $x178))))
(assert
 (let (($x185 (not right_1_4)))
 (let (($x187 (not left_1_5)))
 (or $x187 $x185))))
(assert
 (let (($x193 (not right_1_5)))
 (let (($x187 (not left_1_5)))
 (or $x187 $x193))))
(assert
 (let (($x163 (not right_1_0)))
 (let (($x195 (not left_1_6)))
 (or $x195 $x163))))
(assert
 (let (($x167 (not right_1_1)))
 (let (($x195 (not left_1_6)))
 (or $x195 $x167))))
(assert
 (let (($x172 (not right_1_2)))
 (let (($x195 (not left_1_6)))
 (or $x195 $x172))))
(assert
 (let (($x178 (not right_1_3)))
 (let (($x195 (not left_1_6)))
 (or $x195 $x178))))
(assert
 (let (($x185 (not right_1_4)))
 (let (($x195 (not left_1_6)))
 (or $x195 $x185))))
(assert
 (let (($x193 (not right_1_5)))
 (let (($x195 (not left_1_6)))
 (or $x195 $x193))))
(assert
 (let (($x195 (not left_1_6)))
 (or $x195 (not right_1_6))))
(assert
 (let ((?x230 (ite right_1_6 function_0 (_ bv0 64))))
 (let ((?x228 (ite right_1_5 (_ bv18446744069414584320 64) (_ bv0 64))))
 (let ((?x226 (ite right_1_4 (_ bv18446462603027742720 64) (_ bv0 64))))
 (let ((?x224 (ite right_1_3 (_ bv18374966859414961920 64) (_ bv0 64))))
 (let ((?x222 (ite right_1_2 (_ bv17361641481138401520 64) (_ bv0 64))))
 (let ((?x220 (ite right_1_1 (_ bv14757395258967641292 64) (_ bv0 64))))
 (let ((?x225 (bvor (bvor (bvor (bvor (_ bv0 64) (ite right_1_0 (_ bv12297829382473034410 64) (_ bv0 64))) ?x220) ?x222) ?x224)))
 (let ((?x231 (bvor (bvor (bvor ?x225 ?x226) ?x228) ?x230)))
 (let ((?x216 (ite left_1_6 function_0 (_ bv0 64))))
 (let ((?x214 (ite left_1_5 (_ bv18446744069414584320 64) (_ bv0 64))))
 (let ((?x212 (ite left_1_4 (_ bv18446462603027742720 64) (_ bv0 64))))
 (let ((?x210 (ite left_1_3 (_ bv18374966859414961920 64) (_ bv0 64))))
 (let ((?x208 (ite left_1_2 (_ bv17361641481138401520 64) (_ bv0 64))))
 (let ((?x206 (ite left_1_1 (_ bv14757395258967641292 64) (_ bv0 64))))
 (let ((?x211 (bvor (bvor (bvor (bvor (_ bv0 64) (ite left_1_0 (_ bv12297829382473034410 64) (_ bv0 64))) ?x206) ?x208) ?x210)))
 (let ((?x217 (bvor (bvor (bvor ?x211 ?x212) ?x214) ?x216)))
 (= function_1 (ite is_or_1 (bvor ?x217 ?x231) (bvand ?x217 ?x231))))))))))))))))))))
(assert
 (and (distinct (_ bv12297829382473034410 64) function_1) true))
(assert
 (and (distinct (_ bv14757395258967641292 64) function_1) true))
(assert
 (and (distinct (_ bv17361641481138401520 64) function_1) true))
(assert
 (and (distinct (_ bv18374966859414961920 64) function_1) true))
(assert
 (and (distinct (_ bv18446462603027742720 64) function_1) true))
(assert
 (and (distinct (_ bv18446744069414584320 64) function_1) true))
(assert
 (and (distinct function_1 function_0) true))
(assert
 (=> (not (or left_1_6 right_1_6)) (bvult function_0 function_1)))
(assert
 ((_ pbeq 1 1 1 1 1 1 1 1 1) left_2_0 left_2_1 left_2_2 left_2_3 left_2_4 left_2_5 left_2_6 left_2_7))
(assert
 ((_ pbeq 1 1 1 1 1 1 1 1 1) right_2_0 right_2_1 right_2_2 right_2_3 right_2_4 right_2_5 right_2_6 right_2_7))
(assert
 (let (($x306 (not right_2_0)))
 (or (not left_2_0) $x306)))
(assert
 (let (($x306 (not right_2_0)))
 (let (($x308 (not left_2_1)))
 (or $x308 $x306))))
(assert
 (let (($x310 (not right_2_1)))
 (let (($x308 (not left_2_1)))
 (or $x308 $x310))))
(assert
 (let (($x306 (not right_2_0)))
 (let (($x312 (not left_2_2)))
 (or $x312 $x306))))
(assert
 (let (($x310 (not right_2_1)))
 (let (($x312 (not left_2_2)))
 (or $x312 $x310))))
(assert
 (let (($x315 (not right_2_2)))
 (let (($x312 (not left_2_2)))
 (or $x312 $x315))))
(assert
 (let (($x306 (not right_2_0)))
 (let (($x317 (not left_2_3)))
 (or $x317 $x306))))
(assert
 (let (($x310 (not right_2_1)))
 (let (($x317 (not left_2_3)))
 (or $x317 $x310))))
(assert
 (let (($x315 (not right_2_2)))
 (let (($x317 (not left_2_3)))
 (or $x317 $x315))))
(assert
 (let (($x321 (not right_2_3)))
 (let (($x317 (not left_2_3)))
 (or $x317 $x321))))
(assert
 (let (($x306 (not right_2_0)))
 (let (($x323 (not left_2_4)))
 (or $x323 $x306))))
(assert
 (let (($x310 (not right_2_1)))
 (let (($x323 (not left_2_4)))
 (or $x323 $x310))))
(assert
 (let (($x315 (not right_2_2)))
 (let (($x323 (not left_2_4)))
 (or $x323 $x315))))
(assert
 (let (($x321 (not right_2_3)))
 (let (($x323 (not left_2_4)))
 (or $x323 $x321))))
(assert
 (let (($x328 (not right_2_4)))
 (let (($x323 (not left_2_4)))
 (or $x323 $x328))))
(assert
 (let (($x306 (not right_2_0)))
 (let (($x330 (not left_2_5)))
 (or $x330 $x306))))
(assert
 (let (($x310 (not right_2_1)))
 (let (($x330 (not left_2_5)))
 (or $x330 $x310))))
(assert
 (let (($x315 (not right_2_2)))
 (let (($x330 (not left_2_5)))
 (or $x330 $x315))))
(assert
 (let (($x321 (not right_2_3)))
 (let (($x330 (not left_2_5)))
 (or $x330 $x321))))
(assert
 (let (($x328 (not right_2_4)))
 (let (($x330 (not left_2_5)))
 (or $x330 $x328))))
(assert
 (let (($x336 (not right_2_5)))
 (let (($x330 (not left_2_5)))
 (or $x330 $x336))))
(assert
 (let (($x306 (not right_2_0)))
 (let (($x338 (not left_2_6)))
 (or $x338 $x306))))
(assert
 (let (($x310 (not right_2_1)))
 (let (($x338 (not left_2_6)))
 (or $x338 $x310))))
(assert
 (let (($x315 (not right_2_2)))
 (let (($x338 (not left_2_6)))
 (or $x338 $x315))))
(assert
 (let (($x321 (not right_2_3)))
 (let (($x338 (not left_2_6)))
 (or $x338 $x321))))
(assert
 (let (($x328 (not right_2_4)))
 (let (($x338 (not left_2_6)))
 (or $x338 $x328))))
(assert
 (let (($x336 (not right_2_5)))
 (let (($x338 (not left_2_6)))
 (or $x338 $x336))))
(assert
 (let (($x345 (not right_2_6)))
 (let (($x338 (not left_2_6)))
 (or $x338 $x345))))
(assert
 (let (($x306 (not right_2_0)))
 (let (($x347 (not left_2_7)))
 (or $x347 $x306))))
(assert
 (let (($x310 (not right_2_1)))
 (let (($x347 (not left_2_7)))
 (or $x347 $x310))))
(assert
 (let (($x315 (not right_2_2)))
 (let (($x347 (not left_2_7)))
 (or $x347 $x315))))
(assert
 (let (($x321 (not right_2_3)))
 (let (($x347 (not left_2_7)))
 (or $x347 $x321))))
(assert
 (let (($x328 (not right_2_4)))
 (let (($x347 (not left_2_7)))
 (or $x347 $x328))))
(assert
 (let (($x336 (not right_2_5)))
 (let (($x347 (not left_2_7)))
 (or $x347 $x336))))
(assert
 (let (($x345 (not right_2_6)))
 (let (($x347 (not left_2_7)))
 (or $x347 $x345))))
(assert
 (let (($x347 (not left_2_7)))
 (or $x347 (not right_2_7))))
(assert
 (let ((?x387 (ite right_2_7 function_1 (_ bv0 64))))
 (let ((?x385 (ite right_2_6 function_0 (_ bv0 64))))
 (let ((?x383 (ite right_2_5 (_ bv18446744069414584320 64) (_ bv0 64))))
 (let ((?x381 (ite right_2_4 (_ bv18446462603027742720 64) (_ bv0 64))))
 (let ((?x379 (ite right_2_3 (_ bv18374966859414961920 64) (_ bv0 64))))
 (let ((?x377 (ite right_2_2 (_ bv17361641481138401520 64) (_ bv0 64))))
 (let ((?x375 (ite right_2_1 (_ bv14757395258967641292 64) (_ bv0 64))))
 (let ((?x380 (bvor (bvor (bvor (bvor (_ bv0 64) (ite right_2_0 (_ bv12297829382473034410 64) (_ bv0 64))) ?x375) ?x377) ?x379)))
 (let ((?x388 (bvor (bvor (bvor (bvor ?x380 ?x381) ?x383) ?x385) ?x387)))
 (let ((?x371 (ite left_2_7 function_1 (_ bv0 64))))
 (let ((?x369 (ite left_2_6 function_0 (_ bv0 64))))
 (let ((?x367 (ite left_2_5 (_ bv18446744069414584320 64) (_ bv0 64))))
 (let ((?x365 (ite left_2_4 (_ bv18446462603027742720 64) (_ bv0 64))))
 (let ((?x363 (ite left_2_3 (_ bv18374966859414961920 64) (_ bv0 64))))
 (let ((?x361 (ite left_2_2 (_ bv17361641481138401520 64) (_ bv0 64))))
 (let ((?x359 (ite left_2_1 (_ bv14757395258967641292 64) (_ bv0 64))))
 (let ((?x364 (bvor (bvor (bvor (bvor (_ bv0 64) (ite left_2_0 (_ bv12297829382473034410 64) (_ bv0 64))) ?x359) ?x361) ?x363)))
 (let ((?x372 (bvor (bvor (bvor (bvor ?x364 ?x365) ?x367) ?x369) ?x371)))
 (= function_2 (ite is_or_2 (bvor ?x372 ?x388) (bvand ?x372 ?x388))))))))))))))))))))))
(assert
 (and (distinct (_ bv12297829382473034410 64) function_2) true))
(assert
 (and (distinct (_ bv14757395258967641292 64) function_2) true))
(assert
 (and (distinct (_ bv17361641481138401520 64) function_2) true))
(assert
 (and (distinct (_ bv18374966859414961920 64) function_2) true))
(assert
 (and (distinct (_ bv18446462603027742720 64) function_2) true))
(assert
 (and (distinct (_ bv18446744069414584320 64) function_2) true))
(assert
 (and (distinct function_2 function_0) true))
(assert
 (and (distinct function_2 function_1) true))
(assert
 (=> (not (or left_2_7 right_2_7)) (bvult function_1 function_2)))
(assert
 ((_ pbeq 1 1 1 1 1 1 1 1 1 1) left_3_0 left_3_1 left_3_2 left_3_3 left_3_4 left_3_5 left_3_6 left_3_7 left_3_8))
(assert
 ((_ pbeq 1 1 1 1 1 1 1 1 1 1) right_3_0 right_3_1 right_3_2 right_3_3 right_3_4 right_3_5 right_3_6 right_3_7 right_3_8))
(assert
 (let (($x468 (not right_3_0)))
 (or (not left_3_0) $x468)))
(assert
 (let (($x468 (not right_3_0)))
 (let (($x470 (not left_3_1)))
 (or $x470 $x468))))
(assert
 (let (($x472 (not right_3_1)))
 (let (($x470 (not left_3_1)))
 (or $x470 $x472))))
(assert
 (let (($x468 (not right_3_0)))
 (let (($x474 (not left_3_2)))
 (or $x474 $x468))))
(assert
 (let (($x472 (not right_3_1)))
 (let (($x474 (not left_3_2)))
 (or $x474 $x472))))
(assert
 (let (($x477 (not right_3_2)))
 (let (($x474 (not left_3_2)))
 (or $x474 $x477))))
(assert
 (let (($x468 (not right_3_0)))
 (let (($x479 (not left_3_3)))
 (or $x479 $x468))))
(assert
 (let (($x472 (not right_3_1)))
 (let (($x479 (not left_3_3)))
 (or $x479 $x472))))
(assert
 (let (($x477 (not right_3_2)))
 (let (($x479 (not left_3_3)))
 (or $x479 $x477))))
(assert
 (let (($x483 (not right_3_3)))
 (let (($x479 (not left_3_3)))
 (or $x479 $x483))))
(assert
 (let (($x468 (not right_3_0)))
 (let (($x485 (not left_3_4)))
 (or $x485 $x468))))
(assert
 (let (($x472 (not right_3_1)))
 (let (($x485 (not left_3_4)))
 (or $x485 $x472))))
(assert
 (let (($x477 (not right_3_2)))
 (let (($x485 (not left_3_4)))
 (or $x485 $x477))))
(assert
 (let (($x483 (not right_3_3)))
 (let (($x485 (not left_3_4)))
 (or $x485 $x483))))
(assert
 (let (($x490 (not right_3_4)))
 (let (($x485 (not left_3_4)))
 (or $x485 $x490))))
(assert
 (let (($x468 (not right_3_0)))
 (let (($x492 (not left_3_5)))
 (or $x492 $x468))))
(assert
 (let (($x472 (not right_3_1)))
 (let (($x492 (not left_3_5)))
 (or $x492 $x472))))
(assert
 (let (($x477 (not right_3_2)))
 (let (($x492 (not left_3_5)))
 (or $x492 $x477))))
(assert
 (let (($x483 (not right_3_3)))
 (let (($x492 (not left_3_5)))
 (or $x492 $x483))))
(assert
 (let (($x490 (not right_3_4)))
 (let (($x492 (not left_3_5)))
 (or $x492 $x490))))
(assert
 (let (($x498 (not right_3_5)))
 (let (($x492 (not left_3_5)))
 (or $x492 $x498))))
(assert
 (let (($x468 (not right_3_0)))
 (let (($x500 (not left_3_6)))
 (or $x500 $x468))))
(assert
 (let (($x472 (not right_3_1)))
 (let (($x500 (not left_3_6)))
 (or $x500 $x472))))
(assert
 (let (($x477 (not right_3_2)))
 (let (($x500 (not left_3_6)))
 (or $x500 $x477))))
(assert
 (let (($x483 (not right_3_3)))
 (let (($x500 (not left_3_6)))
 (or $x500 $x483))))
(assert
 (let (($x490 (not right_3_4)))
 (let (($x500 (not left_3_6)))
 (or $x500 $x490))))
(assert
 (let (($x498 (not right_3_5)))
 (let (($x500 (not left_3_6)))
 (or $x500 $x498))))
(assert
 (let (($x507 (not right_3_6)))
 (let (($x500 (not left_3_6)))
 (or $x500 $x507))))
(assert
 (let (($x468 (not right_3_0)))
 (let (($x509 (not left_3_7)))
 (or $x509 $x468))))
(assert
 (let (($x472 (not right_3_1)))
 (let (($x509 (not left_3_7)))
 (or $x509 $x472))))
(assert
 (let (($x477 (not right_3_2)))
 (let (($x509 (not left_3_7)))
 (or $x509 $x477))))
(assert
 (let (($x483 (not right_3_3)))
 (let (($x509 (not left_3_7)))
 (or $x509 $x483))))
(assert
 (let (($x490 (not right_3_4)))
 (let (($x509 (not left_3_7)))
 (or $x509 $x490))))
(assert
 (let (($x498 (not right_3_5)))
 (let (($x509 (not left_3_7)))
 (or $x509 $x498))))
(assert
 (let (($x507 (not right_3_6)))
 (let (($x509 (not left_3_7)))
 (or $x509 $x507))))
(assert
 (let (($x517 (not right_3_7)))
 (let (($x509 (not left_3_7)))
 (or $x509 $x517))))
(assert
 (let (($x468 (not right_3_0)))
 (let (($x519 (not left_3_8)))
 (or $x519 $x468))))
(assert
 (let (($x472 (not right_3_1)))
 (let (($x519 (not left_3_8)))
 (or $x519 $x472))))
(assert
 (let (($x477 (not right_3_2)))
 (let (($x519 (not left_3_8)))
 (or $x519 $x477))))
(assert
 (let (($x483 (not right_3_3)))
 (let (($x519 (not left_3_8)))
 (or $x519 $x483))))
(assert
 (let (($x490 (not right_3_4)))
 (let (($x519 (not left_3_8)))
 (or $x519 $x490))))
(assert
 (let (($x498 (not right_3_5)))
 (let (($x519 (not left_3_8)))
 (or $x519 $x498))))
(assert
 (let (($x507 (not right_3_6)))
 (let (($x519 (not left_3_8)))
 (or $x519 $x507))))
(assert
 (let (($x517 (not right_3_7)))
 (let (($x519 (not left_3_8)))
 (or $x519 $x517))))
(assert
 (let (($x519 (not left_3_8)))
 (or $x519 (not right_3_8))))
(assert
 (let ((?x564 (ite right_3_8 function_2 (_ bv0 64))))
 (let ((?x562 (ite right_3_7 function_1 (_ bv0 64))))
 (let ((?x560 (ite right_3_6 function_0 (_ bv0 64))))
 (let ((?x558 (ite right_3_5 (_ bv18446744069414584320 64) (_ bv0 64))))
 (let ((?x556 (ite right_3_4 (_ bv18446462603027742720 64) (_ bv0 64))))
 (let ((?x554 (ite right_3_3 (_ bv18374966859414961920 64) (_ bv0 64))))
 (let ((?x552 (ite right_3_2 (_ bv17361641481138401520 64) (_ bv0 64))))
 (let ((?x550 (ite right_3_1 (_ bv14757395258967641292 64) (_ bv0 64))))
 (let ((?x555 (bvor (bvor (bvor (bvor (_ bv0 64) (ite right_3_0 (_ bv12297829382473034410 64) (_ bv0 64))) ?x550) ?x552) ?x554)))
 (let ((?x565 (bvor (bvor (bvor (bvor (bvor ?x555 ?x556) ?x558) ?x560) ?x562) ?x564)))
 (let ((?x546 (ite left_3_8 function_2 (_ bv0 64))))
 (let ((?x544 (ite left_3_7 function_1 (_ bv0 64))))
 (let ((?x542 (ite left_3_6 function_0 (_ bv0 64))))
 (let ((?x540 (ite left_3_5 (_ bv18446744069414584320 64) (_ bv0 64))))
 (let ((?x538 (ite left_3_4 (_ bv18446462603027742720 64) (_ bv0 64))))
 (let ((?x536 (ite left_3_3 (_ bv18374966859414961920 64) (_ bv0 64))))
 (let ((?x534 (ite left_3_2 (_ bv17361641481138401520 64) (_ bv0 64))))
 (let ((?x532 (ite left_3_1 (_ bv14757395258967641292 64) (_ bv0 64))))
 (let ((?x537 (bvor (bvor (bvor (bvor (_ bv0 64) (ite left_3_0 (_ bv12297829382473034410 64) (_ bv0 64))) ?x532) ?x534) ?x536)))
 (let ((?x547 (bvor (bvor (bvor (bvor (bvor ?x537 ?x538) ?x540) ?x542) ?x544) ?x546)))
 (= function_3 (ite is_or_3 (bvor ?x547 ?x565) (bvand ?x547 ?x565))))))))))))))))))))))))
(assert
 (and (distinct (_ bv12297829382473034410 64) function_3) true))
(assert
 (and (distinct (_ bv14757395258967641292 64) function_3) true))
(assert
 (and (distinct (_ bv17361641481138401520 64) function_3) true))
(assert
 (and (distinct (_ bv18374966859414961920 64) function_3) true))
(assert
 (and (distinct (_ bv18446462603027742720 64) function_3) true))
(assert
 (and (distinct (_ bv18446744069414584320 64) function_3) true))
(assert
 (and (distinct function_3 function_0) true))
(assert
 (and (distinct function_3 function_1) true))
(assert
 (and (distinct function_3 function_2) true))
(assert
 (=> (not (or left_3_8 right_3_8)) (bvult function_2 function_3)))
(assert
 ((_ pbeq 1 1 1 1 1 1 1 1 1 1 1) left_4_0 left_4_1 left_4_2 left_4_3 left_4_4 left_4_5 left_4_6 left_4_7 left_4_8 left_4_9))
(assert
 ((_ pbeq 1 1 1 1 1 1 1 1 1 1 1) right_4_0 right_4_1 right_4_2 right_4_3 right_4_4 right_4_5 right_4_6 right_4_7 right_4_8 right_4_9))
(assert
 (let (($x650 (not right_4_0)))
 (or (not left_4_0) $x650)))
(assert
 (let (($x650 (not right_4_0)))
 (let (($x652 (not left_4_1)))
 (or $x652 $x650))))
(assert
 (let (($x654 (not right_4_1)))
 (let (($x652 (not left_4_1)))
 (or $x652 $x654))))
(assert
 (let (($x650 (not right_4_0)))
 (let (($x656 (not left_4_2)))
 (or $x656 $x650))))
(assert
 (let (($x654 (not right_4_1)))
 (let (($x656 (not left_4_2)))
 (or $x656 $x654))))
(assert
 (let (($x659 (not right_4_2)))
 (let (($x656 (not left_4_2)))
 (or $x656 $x659))))
(assert
 (let (($x650 (not right_4_0)))
 (let (($x661 (not left_4_3)))
 (or $x661 $x650))))
(assert
 (let (($x654 (not right_4_1)))
 (let (($x661 (not left_4_3)))
 (or $x661 $x654))))
(assert
 (let (($x659 (not right_4_2)))
 (let (($x661 (not left_4_3)))
 (or $x661 $x659))))
(assert
 (let (($x665 (not right_4_3)))
 (let (($x661 (not left_4_3)))
 (or $x661 $x665))))
(assert
 (let (($x650 (not right_4_0)))
 (let (($x667 (not left_4_4)))
 (or $x667 $x650))))
(assert
 (let (($x654 (not right_4_1)))
 (let (($x667 (not left_4_4)))
 (or $x667 $x654))))
(assert
 (let (($x659 (not right_4_2)))
 (let (($x667 (not left_4_4)))
 (or $x667 $x659))))
(assert
 (let (($x665 (not right_4_3)))
 (let (($x667 (not left_4_4)))
 (or $x667 $x665))))
(assert
 (let (($x672 (not right_4_4)))
 (let (($x667 (not left_4_4)))
 (or $x667 $x672))))
(assert
 (let (($x650 (not right_4_0)))
 (let (($x674 (not left_4_5)))
 (or $x674 $x650))))
(assert
 (let (($x654 (not right_4_1)))
 (let (($x674 (not left_4_5)))
 (or $x674 $x654))))
(assert
 (let (($x659 (not right_4_2)))
 (let (($x674 (not left_4_5)))
 (or $x674 $x659))))
(assert
 (let (($x665 (not right_4_3)))
 (let (($x674 (not left_4_5)))
 (or $x674 $x665))))
(assert
 (let (($x672 (not right_4_4)))
 (let (($x674 (not left_4_5)))
 (or $x674 $x672))))
(assert
 (let (($x680 (not right_4_5)))
 (let (($x674 (not left_4_5)))
 (or $x674 $x680))))
(assert
 (let (($x650 (not right_4_0)))
 (let (($x682 (not left_4_6)))
 (or $x682 $x650))))
(assert
 (let (($x654 (not right_4_1)))
 (let (($x682 (not left_4_6)))
 (or $x682 $x654))))
(assert
 (let (($x659 (not right_4_2)))
 (let (($x682 (not left_4_6)))
 (or $x682 $x659))))
(assert
 (let (($x665 (not right_4_3)))
 (let (($x682 (not left_4_6)))
 (or $x682 $x665))))
(assert
 (let (($x672 (not right_4_4)))
 (let (($x682 (not left_4_6)))
 (or $x682 $x672))))
(assert
 (let (($x680 (not right_4_5)))
 (let (($x682 (not left_4_6)))
 (or $x682 $x680))))
(assert
 (let (($x689 (not right_4_6)))
 (let (($x682 (not left_4_6)))
 (or $x682 $x689))))
(assert
 (let (($x650 (not right_4_0)))
 (let (($x691 (not left_4_7)))
 (or $x691 $x650))))
(assert
 (let (($x654 (not right_4_1)))
 (let (($x691 (not left_4_7)))
 (or $x691 $x654))))
(assert
 (let (($x659 (not right_4_2)))
 (let (($x691 (not left_4_7)))
 (or $x691 $x659))))
(assert
 (let (($x665 (not right_4_3)))
 (let (($x691 (not left_4_7)))
 (or $x691 $x665))))
(assert
 (let (($x672 (not right_4_4)))
 (let (($x691 (not left_4_7)))
 (or $x691 $x672))))
(assert
 (let (($x680 (not right_4_5)))
 (let (($x691 (not left_4_7)))
 (or $x691 $x680))))
(assert
 (let (($x689 (not right_4_6)))
 (let (($x691 (not left_4_7)))
 (or $x691 $x689))))
(assert
 (let (($x699 (not right_4_7)))
 (let (($x691 (not left_4_7)))
 (or $x691 $x699))))
(assert
 (let (($x650 (not right_4_0)))
 (let (($x701 (not left_4_8)))
 (or $x701 $x650))))
(assert
 (let (($x654 (not right_4_1)))
 (let (($x701 (not left_4_8)))
 (or $x701 $x654))))
(assert
 (let (($x659 (not right_4_2)))
 (let (($x701 (not left_4_8)))
 (or $x701 $x659))))
(assert
 (let (($x665 (not right_4_3)))
 (let (($x701 (not left_4_8)))
 (or $x701 $x665))))
(assert
 (let (($x672 (not right_4_4)))
 (let (($x701 (not left_4_8)))
 (or $x701 $x672))))
(assert
 (let (($x680 (not right_4_5)))
 (let (($x701 (not left_4_8)))
 (or $x701 $x680))))
(assert
 (let (($x689 (not right_4_6)))
 (let (($x701 (not left_4_8)))
 (or $x701 $x689))))
(assert
 (let (($x699 (not right_4_7)))
 (let (($x701 (not left_4_8)))
 (or $x701 $x699))))
(assert
 (let (($x710 (not right_4_8)))
 (let (($x701 (not left_4_8)))
 (or $x701 $x710))))
(assert
 (let (($x650 (not right_4_0)))
 (let (($x712 (not left_4_9)))
 (or $x712 $x650))))
(assert
 (let (($x654 (not right_4_1)))
 (let (($x712 (not left_4_9)))
 (or $x712 $x654))))
(assert
 (let (($x659 (not right_4_2)))
 (let (($x712 (not left_4_9)))
 (or $x712 $x659))))
(assert
 (let (($x665 (not right_4_3)))
 (let (($x712 (not left_4_9)))
 (or $x712 $x665))))
(assert
 (let (($x672 (not right_4_4)))
 (let (($x712 (not left_4_9)))
 (or $x712 $x672))))
(assert
 (let (($x680 (not right_4_5)))
 (let (($x712 (not left_4_9)))
 (or $x712 $x680))))
(assert
 (let (($x689 (not right_4_6)))
 (let (($x712 (not left_4_9)))
 (or $x712 $x689))))
(assert
 (let (($x699 (not right_4_7)))
 (let (($x712 (not left_4_9)))
 (or $x712 $x699))))
(assert
 (let (($x710 (not right_4_8)))
 (let (($x712 (not left_4_9)))
 (or $x712 $x710))))
(assert
 (let (($x712 (not left_4_9)))
 (or $x712 (not right_4_9))))
(assert
 (let ((?x762 (ite right_4_9 function_3 (_ bv0 64))))
 (let ((?x760 (ite right_4_8 function_2 (_ bv0 64))))
 (let ((?x758 (ite right_4_7 function_1 (_ bv0 64))))
 (let ((?x756 (ite right_4_6 function_0 (_ bv0 64))))
 (let ((?x754 (ite right_4_5 (_ bv18446744069414584320 64) (_ bv0 64))))
 (let ((?x752 (ite right_4_4 (_ bv18446462603027742720 64) (_ bv0 64))))
 (let ((?x750 (ite right_4_3 (_ bv18374966859414961920 64) (_ bv0 64))))
 (let ((?x748 (ite right_4_2 (_ bv17361641481138401520 64) (_ bv0 64))))
 (let ((?x746 (ite right_4_1 (_ bv14757395258967641292 64) (_ bv0 64))))
 (let ((?x751 (bvor (bvor (bvor (bvor (_ bv0 64) (ite right_4_0 (_ bv12297829382473034410 64) (_ bv0 64))) ?x746) ?x748) ?x750)))
 (let ((?x763 (bvor (bvor (bvor (bvor (bvor (bvor ?x751 ?x752) ?x754) ?x756) ?x758) ?x760) ?x762)))
 (let ((?x742 (ite left_4_9 function_3 (_ bv0 64))))
 (let ((?x740 (ite left_4_8 function_2 (_ bv0 64))))
 (let ((?x738 (ite left_4_7 function_1 (_ bv0 64))))
 (let ((?x736 (ite left_4_6 function_0 (_ bv0 64))))
 (let ((?x734 (ite left_4_5 (_ bv18446744069414584320 64) (_ bv0 64))))
 (let ((?x732 (ite left_4_4 (_ bv18446462603027742720 64) (_ bv0 64))))
 (let ((?x730 (ite left_4_3 (_ bv18374966859414961920 64) (_ bv0 64))))
 (let ((?x728 (ite left_4_2 (_ bv17361641481138401520 64) (_ bv0 64))))
 (let ((?x726 (ite left_4_1 (_ bv14757395258967641292 64) (_ bv0 64))))
 (let ((?x731 (bvor (bvor (bvor (bvor (_ bv0 64) (ite left_4_0 (_ bv12297829382473034410 64) (_ bv0 64))) ?x726) ?x728) ?x730)))
 (let ((?x743 (bvor (bvor (bvor (bvor (bvor (bvor ?x731 ?x732) ?x734) ?x736) ?x738) ?x740) ?x742)))
 (= function_4 (ite is_or_4 (bvor ?x743 ?x763) (bvand ?x743 ?x763))))))))))))))))))))))))))
(assert
 (and (distinct (_ bv12297829382473034410 64) function_4) true))
(assert
 (and (distinct (_ bv14757395258967641292 64) function_4) true))
(assert
 (and (distinct (_ bv17361641481138401520 64) function_4) true))
(assert
 (and (distinct (_ bv18374966859414961920 64) function_4) true))
(assert
 (and (distinct (_ bv18446462603027742720 64) function_4) true))
(assert
 (and (distinct (_ bv18446744069414584320 64) function_4) true))
(assert
 (and (distinct function_4 function_0) true))
(assert
 (and (distinct function_4 function_1) true))
(assert
 (and (distinct function_4 function_2) true))
(assert
 (and (distinct function_4 function_3) true))
(assert
 (=> (not (or left_4_9 right_4_9)) (bvult function_3 function_4)))
(assert
 (or left_1_6 right_1_6 left_2_6 right_2_6 left_3_6 right_3_6 left_4_6 right_4_6))
(assert
 (or left_2_7 right_2_7 left_3_7 right_3_7 left_4_7 right_4_7))
(assert
 (or left_3_8 right_3_8 left_4_8 right_4_8))
(assert
 (or left_4_9 right_4_9))
(assert
 (= (_ bv18374403892280490496 64) function_4))
(check-sat)
