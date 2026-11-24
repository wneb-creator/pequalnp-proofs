; benchmark generated from python API
(set-info :status unknown)
(declare-fun active0 () Bool)
(declare-fun b0 () (_ BitVec 4))
(declare-fun a0 () (_ BitVec 4))
(declare-fun and0 () Bool)
(declare-fun w0 () (_ BitVec 27))
(declare-fun b4 () (_ BitVec 4))
(declare-fun a4 () (_ BitVec 4))
(declare-fun active4 () Bool)
(declare-fun b3 () (_ BitVec 4))
(declare-fun a3 () (_ BitVec 4))
(declare-fun active3 () Bool)
(declare-fun b2 () (_ BitVec 4))
(declare-fun a2 () (_ BitVec 4))
(declare-fun active2 () Bool)
(declare-fun b1 () (_ BitVec 4))
(declare-fun a1 () (_ BitVec 4))
(declare-fun active1 () Bool)
(declare-fun and1 () Bool)
(declare-fun w1 () (_ BitVec 27))
(declare-fun and2 () Bool)
(declare-fun w2 () (_ BitVec 27))
(declare-fun and3 () Bool)
(declare-fun w3 () (_ BitVec 27))
(declare-fun and4 () Bool)
(declare-fun w4 () (_ BitVec 27))
(assert
 active0)
(assert
 (bvult b0 (_ bv8 4)))
(assert
 (=> active0 (bvult a0 b0)))
(assert
 (let (($x69 (= b0 (_ bv4 4))))
 (let ((?x70 (ite $x69 (_ bv67109360 27) (ite (= b0 (_ bv5 4)) (_ bv100679168 27) (ite (= b0 (_ bv6 4)) (_ bv117948416 27) (_ bv133693440 27))))))
 (let (($x71 (= b0 (_ bv3 4))))
 (let (($x73 (= b0 (_ bv2 4))))
 (let (($x75 (= b0 (_ bv1 4))))
 (let ((?x78 (ite (= b0 (_ bv0 4)) (_ bv118522913 27) (ite $x75 (_ bv119605314 27) (ite $x73 (_ bv54661252 27) (ite $x71 (_ bv25436424 27) ?x70))))))
 (let ((?x52 (ite (= a0 (_ bv4 4)) (_ bv67109360 27) (ite (= a0 (_ bv5 4)) (_ bv100679168 27) (ite (= a0 (_ bv6 4)) (_ bv117948416 27) (_ bv133693440 27))))))
 (let (($x54 (= a0 (_ bv3 4))))
 (let (($x57 (= a0 (_ bv2 4))))
 (let (($x63 (= a0 (_ bv0 4))))
 (let ((?x64 (ite $x63 (_ bv118522913 27) (ite (= a0 (_ bv1 4)) (_ bv119605314 27) (ite $x57 (_ bv54661252 27) (ite $x54 (_ bv25436424 27) ?x52))))))
 (= w0 (ite and0 (bvand ?x64 ?x78) (bvor ?x64 ?x78)))))))))))))))
(assert
 (let (($x91 (and (and (distinct (_ bv118522913 27) w0) true) (and (distinct (_ bv119605314 27) w0) true) (and (distinct (_ bv54661252 27) w0) true) (and (distinct (_ bv25436424 27) w0) true) (and (distinct (_ bv67109360 27) w0) true) (and (distinct (_ bv100679168 27) w0) true) (and (distinct (_ bv117948416 27) w0) true) (and (distinct (_ bv133693440 27) w0) true))))
 (=> active0 $x91)))
(assert
 (let (($x109 (or (and active1 (or (= a1 (_ bv8 4)) (= b1 (_ bv8 4)))) (and active2 (or (= a2 (_ bv8 4)) (= b2 (_ bv8 4)))) (and active3 (or (= a3 (_ bv8 4)) (= b3 (_ bv8 4)))) (and active4 (or (= a4 (_ bv8 4)) (= b4 (_ bv8 4)))))))
 (let (($x110 (not active1)))
 (=> active0 (or $x110 $x109)))))
(assert
 (bvult b1 (_ bv9 4)))
(assert
 (=> active1 (bvult a1 b1)))
(assert
 (=> active1 active0))
(assert
 (let (($x110 (not active1)))
 (=> $x110 (and (= a1 (_ bv8 4)) (= b1 (_ bv8 4)) (not and1)))))
(assert
 (let ((?x143 (ite (= b1 (_ bv5 4)) (_ bv100679168 27) (ite (= b1 (_ bv6 4)) (_ bv117948416 27) (ite (= b1 (_ bv7 4)) (_ bv133693440 27) w0)))))
 (let ((?x149 (ite (= b1 (_ bv2 4)) (_ bv54661252 27) (ite (= b1 (_ bv3 4)) (_ bv25436424 27) (ite (= b1 (_ bv4 4)) (_ bv67109360 27) ?x143)))))
 (let ((?x153 (ite (= b1 (_ bv0 4)) (_ bv118522913 27) (ite (= b1 (_ bv1 4)) (_ bv119605314 27) ?x149))))
 (let ((?x127 (ite (= a1 (_ bv5 4)) (_ bv100679168 27) (ite (= a1 (_ bv6 4)) (_ bv117948416 27) (ite (= a1 (_ bv7 4)) (_ bv133693440 27) w0)))))
 (let ((?x133 (ite (= a1 (_ bv2 4)) (_ bv54661252 27) (ite (= a1 (_ bv3 4)) (_ bv25436424 27) (ite (= a1 (_ bv4 4)) (_ bv67109360 27) ?x127)))))
 (let ((?x137 (ite (= a1 (_ bv0 4)) (_ bv118522913 27) (ite (= a1 (_ bv1 4)) (_ bv119605314 27) ?x133))))
 (= w1 (ite and1 (bvand ?x137 ?x153) (bvor ?x137 ?x153))))))))))
(assert
 (let (($x167 (and (and (distinct (_ bv118522913 27) w1) true) (and (distinct (_ bv119605314 27) w1) true) (and (distinct (_ bv54661252 27) w1) true) (and (distinct (_ bv25436424 27) w1) true) (and (distinct (_ bv67109360 27) w1) true) (and (distinct (_ bv100679168 27) w1) true) (and (distinct (_ bv117948416 27) w1) true) (and (distinct (_ bv133693440 27) w1) true) (and (distinct w1 w0) true))))
 (=> active1 $x167)))
(assert
 (let (($x181 (or (and active2 (or (= a2 (_ bv9 4)) (= b2 (_ bv9 4)))) (and active3 (or (= a3 (_ bv9 4)) (= b3 (_ bv9 4)))) (and active4 (or (= a4 (_ bv9 4)) (= b4 (_ bv9 4)))))))
 (let (($x182 (not active2)))
 (=> active1 (or $x182 $x181)))))
(assert
 (bvult b2 (_ bv10 4)))
(assert
 (=> active2 (bvult a2 b2)))
(assert
 (=> active2 active1))
(assert
 (let (($x182 (not active2)))
 (=> $x182 (and (= a2 (_ bv9 4)) (= b2 (_ bv9 4)) (not and2)))))
(assert
 (let ((?x214 (ite (= b2 (_ bv6 4)) (_ bv117948416 27) (ite (= b2 (_ bv7 4)) (_ bv133693440 27) (ite (= b2 (_ bv8 4)) w0 w1)))))
 (let ((?x220 (ite (= b2 (_ bv3 4)) (_ bv25436424 27) (ite (= b2 (_ bv4 4)) (_ bv67109360 27) (ite (= b2 (_ bv5 4)) (_ bv100679168 27) ?x214)))))
 (let ((?x226 (ite (= b2 (_ bv0 4)) (_ bv118522913 27) (ite (= b2 (_ bv1 4)) (_ bv119605314 27) (ite (= b2 (_ bv2 4)) (_ bv54661252 27) ?x220)))))
 (let ((?x197 (ite (= a2 (_ bv6 4)) (_ bv117948416 27) (ite (= a2 (_ bv7 4)) (_ bv133693440 27) (ite (= a2 (_ bv8 4)) w0 w1)))))
 (let ((?x203 (ite (= a2 (_ bv3 4)) (_ bv25436424 27) (ite (= a2 (_ bv4 4)) (_ bv67109360 27) (ite (= a2 (_ bv5 4)) (_ bv100679168 27) ?x197)))))
 (let ((?x209 (ite (= a2 (_ bv0 4)) (_ bv118522913 27) (ite (= a2 (_ bv1 4)) (_ bv119605314 27) (ite (= a2 (_ bv2 4)) (_ bv54661252 27) ?x203)))))
 (= w2 (ite and2 (bvand ?x209 ?x226) (bvor ?x209 ?x226))))))))))
(assert
 (let (($x241 (and (and (distinct (_ bv118522913 27) w2) true) (and (distinct (_ bv119605314 27) w2) true) (and (distinct (_ bv54661252 27) w2) true) (and (distinct (_ bv25436424 27) w2) true) (and (distinct (_ bv67109360 27) w2) true) (and (distinct (_ bv100679168 27) w2) true) (and (distinct (_ bv117948416 27) w2) true) (and (distinct (_ bv133693440 27) w2) true) (and (distinct w2 w0) true) (and (distinct w2 w1) true))))
 (=> active2 $x241)))
(assert
 (let (($x251 (or (and active3 (or (= a3 (_ bv10 4)) (= b3 (_ bv10 4)))) (and active4 (or (= a4 (_ bv10 4)) (= b4 (_ bv10 4)))))))
 (let (($x252 (not active3)))
 (=> active2 (or $x252 $x251)))))
(assert
 (bvult b3 (_ bv11 4)))
(assert
 (=> active3 (bvult a3 b3)))
(assert
 (=> active3 active2))
(assert
 (let (($x252 (not active3)))
 (=> $x252 (and (= a3 (_ bv10 4)) (= b3 (_ bv10 4)) (not and3)))))
(assert
 (let ((?x284 (ite (= b3 (_ bv7 4)) (_ bv133693440 27) (ite (= b3 (_ bv8 4)) w0 (ite (= b3 (_ bv9 4)) w1 w2)))))
 (let ((?x290 (ite (= b3 (_ bv4 4)) (_ bv67109360 27) (ite (= b3 (_ bv5 4)) (_ bv100679168 27) (ite (= b3 (_ bv6 4)) (_ bv117948416 27) ?x284)))))
 (let ((?x296 (ite (= b3 (_ bv1 4)) (_ bv119605314 27) (ite (= b3 (_ bv2 4)) (_ bv54661252 27) (ite (= b3 (_ bv3 4)) (_ bv25436424 27) ?x290)))))
 (let ((?x298 (ite (= b3 (_ bv0 4)) (_ bv118522913 27) ?x296)))
 (let ((?x266 (ite (= a3 (_ bv7 4)) (_ bv133693440 27) (ite (= a3 (_ bv8 4)) w0 (ite (= a3 (_ bv9 4)) w1 w2)))))
 (let ((?x272 (ite (= a3 (_ bv4 4)) (_ bv67109360 27) (ite (= a3 (_ bv5 4)) (_ bv100679168 27) (ite (= a3 (_ bv6 4)) (_ bv117948416 27) ?x266)))))
 (let ((?x278 (ite (= a3 (_ bv1 4)) (_ bv119605314 27) (ite (= a3 (_ bv2 4)) (_ bv54661252 27) (ite (= a3 (_ bv3 4)) (_ bv25436424 27) ?x272)))))
 (let ((?x280 (ite (= a3 (_ bv0 4)) (_ bv118522913 27) ?x278)))
 (= w3 (ite and3 (bvand ?x280 ?x298) (bvor ?x280 ?x298))))))))))))
(assert
 (let (($x314 (and (and (distinct (_ bv118522913 27) w3) true) (and (distinct (_ bv119605314 27) w3) true) (and (distinct (_ bv54661252 27) w3) true) (and (distinct (_ bv25436424 27) w3) true) (and (distinct (_ bv67109360 27) w3) true) (and (distinct (_ bv100679168 27) w3) true) (and (distinct (_ bv117948416 27) w3) true) (and (distinct (_ bv133693440 27) w3) true) (and (distinct w3 w0) true) (and (distinct w3 w1) true) (and (distinct w3 w2) true))))
 (=> active3 $x314)))
(assert
 (let (($x320 (or (and active4 (or (= a4 (_ bv11 4)) (= b4 (_ bv11 4)))))))
 (let (($x321 (not active4)))
 (=> active3 (or $x321 $x320)))))
(assert
 (bvult b4 (_ bv12 4)))
(assert
 (=> active4 (bvult a4 b4)))
(assert
 (=> active4 active3))
(assert
 (let (($x321 (not active4)))
 (=> $x321 (and (= a4 (_ bv11 4)) (= b4 (_ bv11 4)) (not and4)))))
(assert
 (let (($x106 (= b4 (_ bv8 4))))
 (let ((?x353 (ite $x106 w0 (ite (= b4 (_ bv9 4)) w1 (ite (= b4 (_ bv10 4)) w2 w3)))))
 (let ((?x359 (ite (= b4 (_ bv5 4)) (_ bv100679168 27) (ite (= b4 (_ bv6 4)) (_ bv117948416 27) (ite (= b4 (_ bv7 4)) (_ bv133693440 27) ?x353)))))
 (let ((?x365 (ite (= b4 (_ bv2 4)) (_ bv54661252 27) (ite (= b4 (_ bv3 4)) (_ bv25436424 27) (ite (= b4 (_ bv4 4)) (_ bv67109360 27) ?x359)))))
 (let ((?x369 (ite (= b4 (_ bv0 4)) (_ bv118522913 27) (ite (= b4 (_ bv1 4)) (_ bv119605314 27) ?x365))))
 (let (($x105 (= a4 (_ bv8 4))))
 (let ((?x334 (ite $x105 w0 (ite (= a4 (_ bv9 4)) w1 (ite (= a4 (_ bv10 4)) w2 w3)))))
 (let ((?x340 (ite (= a4 (_ bv5 4)) (_ bv100679168 27) (ite (= a4 (_ bv6 4)) (_ bv117948416 27) (ite (= a4 (_ bv7 4)) (_ bv133693440 27) ?x334)))))
 (let ((?x346 (ite (= a4 (_ bv2 4)) (_ bv54661252 27) (ite (= a4 (_ bv3 4)) (_ bv25436424 27) (ite (= a4 (_ bv4 4)) (_ bv67109360 27) ?x340)))))
 (let ((?x350 (ite (= a4 (_ bv0 4)) (_ bv118522913 27) (ite (= a4 (_ bv1 4)) (_ bv119605314 27) ?x346))))
 (= w4 (ite and4 (bvand ?x350 ?x369) (bvor ?x350 ?x369))))))))))))))
(assert
 (let (($x386 (and (and (distinct (_ bv118522913 27) w4) true) (and (distinct (_ bv119605314 27) w4) true) (and (distinct (_ bv54661252 27) w4) true) (and (distinct (_ bv25436424 27) w4) true) (and (distinct (_ bv67109360 27) w4) true) (and (distinct (_ bv100679168 27) w4) true) (and (distinct (_ bv117948416 27) w4) true) (and (distinct (_ bv133693440 27) w4) true) (and (distinct w4 w0) true) (and (distinct w4 w1) true) (and (distinct w4 w2) true) (and (distinct w4 w3) true))))
 (=> active4 $x386)))
(assert
 (let (($x398 (and (= a0 a1) (or (bvult b0 b1) (and (= b0 b1) (or and0 (not and1)))))))
 (=> (and active0 active1 (and (distinct a1 (_ bv8 4)) true) (and (distinct b1 (_ bv8 4)) true)) (or (bvult a0 a1) $x398))))
(assert
 (let (($x411 (and (= a1 a2) (or (bvult b1 b2) (and (= b1 b2) (or and1 (not and2)))))))
 (=> (and active1 active2 (and (distinct a2 (_ bv9 4)) true) (and (distinct b2 (_ bv9 4)) true)) (or (bvult a1 a2) $x411))))
(assert
 (let (($x424 (and (= a2 a3) (or (bvult b2 b3) (and (= b2 b3) (or and2 (not and3)))))))
 (=> (and active2 active3 (and (distinct a3 (_ bv10 4)) true) (and (distinct b3 (_ bv10 4)) true)) (or (bvult a2 a3) $x424))))
(assert
 (let (($x437 (and (= a3 a4) (or (bvult b3 b4) (and (= b3 b4) (or and3 (not and4)))))))
 (let (($x438 (or (bvult a3 a4) $x437)))
 (let (($x429 (and active3 active4 (and (distinct a4 (_ bv11 4)) true) (and (distinct b4 (_ bv11 4)) true))))
 (=> $x429 $x438)))))
(assert
 (let (($x69 (= b0 (_ bv4 4))))
 (let (($x54 (= a0 (_ bv3 4))))
 (let (($x449 (and $x54 $x69)))
 (let (($x67 (= b0 (_ bv5 4))))
 (let (($x57 (= a0 (_ bv2 4))))
 (let (($x448 (and $x57 $x67)))
 (let (($x447 (and $x57 $x69)))
 (let (($x71 (= b0 (_ bv3 4))))
 (let (($x446 (and $x57 $x71)))
 (let (($x65 (= b0 (_ bv6 4))))
 (let (($x63 (= a0 (_ bv0 4))))
 (let (($x445 (and $x63 $x65)))
 (let (($x444 (and $x63 $x67)))
 (let (($x443 (and $x63 $x69)))
 (let (($x442 (and $x63 $x71)))
 (let (($x73 (= b0 (_ bv2 4))))
 (let (($x441 (and $x63 $x73)))
 (let (($x75 (= b0 (_ bv1 4))))
 (let (($x440 (and $x63 $x75)))
 (or $x440 $x441 $x442 $x443 $x444 $x445 $x446 $x447 $x448 $x449)))))))))))))))))))))
(assert
 (= w4 (_ bv8576 27)))
(check-sat)
