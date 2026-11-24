; benchmark generated from python API
(set-info :status unknown)
(declare-fun active0 () Bool)
(declare-fun active3 () Bool)
(declare-fun b3 () (_ BitVec 4))
(declare-fun a3 () (_ BitVec 4))
(declare-fun b2 () (_ BitVec 4))
(declare-fun a2 () (_ BitVec 4))
(declare-fun active2 () Bool)
(declare-fun b1 () (_ BitVec 4))
(declare-fun a1 () (_ BitVec 4))
(declare-fun active1 () Bool)
(declare-fun b0 () (_ BitVec 4))
(declare-fun a0 () (_ BitVec 4))
(declare-fun and0 () Bool)
(declare-fun w0 () (_ BitVec 27))
(declare-fun and1 () Bool)
(declare-fun w1 () (_ BitVec 27))
(declare-fun and2 () Bool)
(declare-fun w2 () (_ BitVec 27))
(declare-fun and3 () Bool)
(declare-fun w3 () (_ BitVec 27))
(assert
 active0)
(assert
 active3)
(assert
 (or (and active0 (or (= a0 (_ bv2 4)) (= b0 (_ bv2 4)))) (and active1 (or (= a1 (_ bv2 4)) (= b1 (_ bv2 4)))) (and active2 (or (= a2 (_ bv2 4)) (= b2 (_ bv2 4)))) (and active3 (or (= a3 (_ bv2 4)) (= b3 (_ bv2 4))))))
(assert
 (or (and active0 (or (= a0 (_ bv3 4)) (= b0 (_ bv3 4)))) (and active1 (or (= a1 (_ bv3 4)) (= b1 (_ bv3 4)))) (and active2 (or (= a2 (_ bv3 4)) (= b2 (_ bv3 4)))) (and active3 (or (= a3 (_ bv3 4)) (= b3 (_ bv3 4))))))
(assert
 (or (and active0 (or (= a0 (_ bv4 4)) (= b0 (_ bv4 4)))) (and active1 (or (= a1 (_ bv4 4)) (= b1 (_ bv4 4)))) (and active2 (or (= a2 (_ bv4 4)) (= b2 (_ bv4 4)))) (and active3 (or (= a3 (_ bv4 4)) (= b3 (_ bv4 4))))))
(assert
 (or (and active0 (or (= a0 (_ bv5 4)) (= b0 (_ bv5 4)))) (and active1 (or (= a1 (_ bv5 4)) (= b1 (_ bv5 4)))) (and active2 (or (= a2 (_ bv5 4)) (= b2 (_ bv5 4)))) (and active3 (or (= a3 (_ bv5 4)) (= b3 (_ bv5 4))))))
(assert
 (or (and active0 (or (= a0 (_ bv6 4)) (= b0 (_ bv6 4)))) (and active1 (or (= a1 (_ bv6 4)) (= b1 (_ bv6 4)))) (and active2 (or (= a2 (_ bv6 4)) (= b2 (_ bv6 4)))) (and active3 (or (= a3 (_ bv6 4)) (= b3 (_ bv6 4))))))
(assert
 (bvult b0 (_ bv8 4)))
(assert
 (=> active0 (bvult a0 b0)))
(assert
 (=> active0 (and (and (distinct a0 (_ bv0 4)) true) (and (distinct b0 (_ bv0 4)) true))))
(assert
 (=> active0 (and (and (distinct a0 (_ bv1 4)) true) (and (distinct b0 (_ bv1 4)) true))))
(assert
 (=> active0 (and (and (distinct a0 (_ bv7 4)) true) (and (distinct b0 (_ bv7 4)) true))))
(assert
 (let (($x73 (= b0 (_ bv4 4))))
 (let ((?x155 (ite $x73 (_ bv67109360 27) (ite (= b0 (_ bv5 4)) (_ bv100679168 27) (ite (= b0 (_ bv6 4)) (_ bv101171200 27) (_ bv133693440 27))))))
 (let (($x55 (= b0 (_ bv3 4))))
 (let (($x37 (= b0 (_ bv2 4))))
 (let (($x158 (= b0 (_ bv1 4))))
 (let ((?x161 (ite (= b0 (_ bv0 4)) (_ bv118522913 27) (ite $x158 (_ bv119605314 27) (ite $x37 (_ bv54661252 27) (ite $x55 (_ bv25436424 27) ?x155))))))
 (let (($x72 (= a0 (_ bv4 4))))
 (let ((?x146 (ite $x72 (_ bv67109360 27) (ite (= a0 (_ bv5 4)) (_ bv100679168 27) (ite (= a0 (_ bv6 4)) (_ bv101171200 27) (_ bv133693440 27))))))
 (let (($x54 (= a0 (_ bv3 4))))
 (let (($x36 (= a0 (_ bv2 4))))
 (let (($x151 (= a0 (_ bv0 4))))
 (let ((?x152 (ite $x151 (_ bv118522913 27) (ite (= a0 (_ bv1 4)) (_ bv119605314 27) (ite $x36 (_ bv54661252 27) (ite $x54 (_ bv25436424 27) ?x146))))))
 (= w0 (ite and0 (bvand ?x152 ?x161) (bvor ?x152 ?x161))))))))))))))))
(assert
 (let (($x174 (and (and (distinct (_ bv118522913 27) w0) true) (and (distinct (_ bv119605314 27) w0) true) (and (distinct (_ bv54661252 27) w0) true) (and (distinct (_ bv25436424 27) w0) true) (and (distinct (_ bv67109360 27) w0) true) (and (distinct (_ bv100679168 27) w0) true) (and (distinct (_ bv101171200 27) w0) true) (and (distinct (_ bv133693440 27) w0) true))))
 (=> active0 $x174)))
(assert
 (let (($x188 (or (and active1 (or (= a1 (_ bv8 4)) (= b1 (_ bv8 4)))) (and active2 (or (= a2 (_ bv8 4)) (= b2 (_ bv8 4)))) (and active3 (or (= a3 (_ bv8 4)) (= b3 (_ bv8 4)))))))
 (let (($x189 (not active1)))
 (=> active0 (or $x189 $x188)))))
(assert
 (bvult b1 (_ bv9 4)))
(assert
 (=> active1 (bvult a1 b1)))
(assert
 (=> active1 (and (and (distinct a1 (_ bv0 4)) true) (and (distinct b1 (_ bv0 4)) true))))
(assert
 (=> active1 (and (and (distinct a1 (_ bv1 4)) true) (and (distinct b1 (_ bv1 4)) true))))
(assert
 (=> active1 (and (and (distinct a1 (_ bv7 4)) true) (and (distinct b1 (_ bv7 4)) true))))
(assert
 (=> active1 active0))
(assert
 (let (($x189 (not active1)))
 (=> $x189 (and (= a1 (_ bv8 4)) (= b1 (_ bv8 4)) (not and1)))))
(assert
 (let (($x95 (= b1 (_ bv5 4))))
 (let ((?x226 (ite $x95 (_ bv100679168 27) (ite (= b1 (_ bv6 4)) (_ bv101171200 27) (ite (= b1 (_ bv7 4)) (_ bv133693440 27) w0)))))
 (let (($x77 (= b1 (_ bv4 4))))
 (let (($x59 (= b1 (_ bv3 4))))
 (let (($x41 (= b1 (_ bv2 4))))
 (let ((?x231 (ite (= b1 (_ bv1 4)) (_ bv119605314 27) (ite $x41 (_ bv54661252 27) (ite $x59 (_ bv25436424 27) (ite $x77 (_ bv67109360 27) ?x226))))))
 (let ((?x233 (ite (= b1 (_ bv0 4)) (_ bv118522913 27) ?x231)))
 (let (($x94 (= a1 (_ bv5 4))))
 (let ((?x215 (ite $x94 (_ bv100679168 27) (ite (= a1 (_ bv6 4)) (_ bv101171200 27) (ite (= a1 (_ bv7 4)) (_ bv133693440 27) w0)))))
 (let (($x76 (= a1 (_ bv4 4))))
 (let (($x58 (= a1 (_ bv3 4))))
 (let (($x40 (= a1 (_ bv2 4))))
 (let ((?x220 (ite (= a1 (_ bv1 4)) (_ bv119605314 27) (ite $x40 (_ bv54661252 27) (ite $x58 (_ bv25436424 27) (ite $x76 (_ bv67109360 27) ?x215))))))
 (let ((?x222 (ite (= a1 (_ bv0 4)) (_ bv118522913 27) ?x220)))
 (= w1 (ite and1 (bvand ?x222 ?x233) (bvor ?x222 ?x233))))))))))))))))))
(assert
 (let (($x247 (and (and (distinct (_ bv118522913 27) w1) true) (and (distinct (_ bv119605314 27) w1) true) (and (distinct (_ bv54661252 27) w1) true) (and (distinct (_ bv25436424 27) w1) true) (and (distinct (_ bv67109360 27) w1) true) (and (distinct (_ bv100679168 27) w1) true) (and (distinct (_ bv101171200 27) w1) true) (and (distinct (_ bv133693440 27) w1) true) (and (distinct w1 w0) true))))
 (=> active1 $x247)))
(assert
 (let (($x257 (or (and active2 (or (= a2 (_ bv9 4)) (= b2 (_ bv9 4)))) (and active3 (or (= a3 (_ bv9 4)) (= b3 (_ bv9 4)))))))
 (let (($x258 (not active2)))
 (=> active1 (or $x258 $x257)))))
(assert
 (bvult b2 (_ bv10 4)))
(assert
 (=> active2 (bvult a2 b2)))
(assert
 (=> active2 (and (and (distinct a2 (_ bv0 4)) true) (and (distinct b2 (_ bv0 4)) true))))
(assert
 (=> active2 (and (and (distinct a2 (_ bv1 4)) true) (and (distinct b2 (_ bv1 4)) true))))
(assert
 (=> active2 (and (and (distinct a2 (_ bv7 4)) true) (and (distinct b2 (_ bv7 4)) true))))
(assert
 (=> active2 active1))
(assert
 (let (($x258 (not active2)))
 (=> $x258 (and (= a2 (_ bv9 4)) (= b2 (_ bv9 4)) (not and2)))))
(assert
 (let (($x117 (= b2 (_ bv6 4))))
 (let ((?x296 (ite $x117 (_ bv101171200 27) (ite (= b2 (_ bv7 4)) (_ bv133693440 27) (ite (= b2 (_ bv8 4)) w0 w1)))))
 (let (($x99 (= b2 (_ bv5 4))))
 (let (($x81 (= b2 (_ bv4 4))))
 (let (($x63 (= b2 (_ bv3 4))))
 (let (($x45 (= b2 (_ bv2 4))))
 (let ((?x302 (ite (= b2 (_ bv1 4)) (_ bv119605314 27) (ite $x45 (_ bv54661252 27) (ite $x63 (_ bv25436424 27) (ite $x81 (_ bv67109360 27) (ite $x99 (_ bv100679168 27) ?x296)))))))
 (let ((?x304 (ite (= b2 (_ bv0 4)) (_ bv118522913 27) ?x302)))
 (let (($x116 (= a2 (_ bv6 4))))
 (let ((?x284 (ite $x116 (_ bv101171200 27) (ite (= a2 (_ bv7 4)) (_ bv133693440 27) (ite (= a2 (_ bv8 4)) w0 w1)))))
 (let (($x98 (= a2 (_ bv5 4))))
 (let (($x80 (= a2 (_ bv4 4))))
 (let (($x62 (= a2 (_ bv3 4))))
 (let (($x44 (= a2 (_ bv2 4))))
 (let ((?x290 (ite (= a2 (_ bv1 4)) (_ bv119605314 27) (ite $x44 (_ bv54661252 27) (ite $x62 (_ bv25436424 27) (ite $x80 (_ bv67109360 27) (ite $x98 (_ bv100679168 27) ?x284)))))))
 (let ((?x292 (ite (= a2 (_ bv0 4)) (_ bv118522913 27) ?x290)))
 (= w2 (ite and2 (bvand ?x292 ?x304) (bvor ?x292 ?x304))))))))))))))))))))
(assert
 (let (($x319 (and (and (distinct (_ bv118522913 27) w2) true) (and (distinct (_ bv119605314 27) w2) true) (and (distinct (_ bv54661252 27) w2) true) (and (distinct (_ bv25436424 27) w2) true) (and (distinct (_ bv67109360 27) w2) true) (and (distinct (_ bv100679168 27) w2) true) (and (distinct (_ bv101171200 27) w2) true) (and (distinct (_ bv133693440 27) w2) true) (and (distinct w2 w0) true) (and (distinct w2 w1) true))))
 (=> active2 $x319)))
(assert
 (let (($x325 (or (and active3 (or (= a3 (_ bv10 4)) (= b3 (_ bv10 4)))))))
 (let (($x326 (not active3)))
 (=> active2 (or $x326 $x325)))))
(assert
 (bvult b3 (_ bv11 4)))
(assert
 (=> active3 (bvult a3 b3)))
(assert
 (=> active3 (and (and (distinct a3 (_ bv0 4)) true) (and (distinct b3 (_ bv0 4)) true))))
(assert
 (=> active3 (and (and (distinct a3 (_ bv1 4)) true) (and (distinct b3 (_ bv1 4)) true))))
(assert
 (=> active3 (and (and (distinct a3 (_ bv7 4)) true) (and (distinct b3 (_ bv7 4)) true))))
(assert
 (=> active3 active2))
(assert
 (let (($x326 (not active3)))
 (=> $x326 (and (= a3 (_ bv10 4)) (= b3 (_ bv10 4)) (not and3)))))
(assert
 (let ((?x365 (ite (= b3 (_ bv7 4)) (_ bv133693440 27) (ite (= b3 (_ bv8 4)) w0 (ite (= b3 (_ bv9 4)) w1 w2)))))
 (let (($x121 (= b3 (_ bv6 4))))
 (let (($x103 (= b3 (_ bv5 4))))
 (let (($x85 (= b3 (_ bv4 4))))
 (let (($x67 (= b3 (_ bv3 4))))
 (let (($x49 (= b3 (_ bv2 4))))
 (let ((?x370 (ite $x49 (_ bv54661252 27) (ite $x67 (_ bv25436424 27) (ite $x85 (_ bv67109360 27) (ite $x103 (_ bv100679168 27) (ite $x121 (_ bv101171200 27) ?x365)))))))
 (let ((?x374 (ite (= b3 (_ bv0 4)) (_ bv118522913 27) (ite (= b3 (_ bv1 4)) (_ bv119605314 27) ?x370))))
 (let ((?x352 (ite (= a3 (_ bv7 4)) (_ bv133693440 27) (ite (= a3 (_ bv8 4)) w0 (ite (= a3 (_ bv9 4)) w1 w2)))))
 (let (($x120 (= a3 (_ bv6 4))))
 (let (($x102 (= a3 (_ bv5 4))))
 (let (($x84 (= a3 (_ bv4 4))))
 (let (($x66 (= a3 (_ bv3 4))))
 (let (($x48 (= a3 (_ bv2 4))))
 (let ((?x357 (ite $x48 (_ bv54661252 27) (ite $x66 (_ bv25436424 27) (ite $x84 (_ bv67109360 27) (ite $x102 (_ bv100679168 27) (ite $x120 (_ bv101171200 27) ?x352)))))))
 (let ((?x361 (ite (= a3 (_ bv0 4)) (_ bv118522913 27) (ite (= a3 (_ bv1 4)) (_ bv119605314 27) ?x357))))
 (= w3 (ite and3 (bvand ?x361 ?x374) (bvor ?x361 ?x374))))))))))))))))))))
(assert
 (let (($x390 (and (and (distinct (_ bv118522913 27) w3) true) (and (distinct (_ bv119605314 27) w3) true) (and (distinct (_ bv54661252 27) w3) true) (and (distinct (_ bv25436424 27) w3) true) (and (distinct (_ bv67109360 27) w3) true) (and (distinct (_ bv100679168 27) w3) true) (and (distinct (_ bv101171200 27) w3) true) (and (distinct (_ bv133693440 27) w3) true) (and (distinct w3 w0) true) (and (distinct w3 w1) true) (and (distinct w3 w2) true))))
 (=> active3 $x390)))
(assert
 (let (($x402 (and (= a0 a1) (or (bvult b0 b1) (and (= b0 b1) (or and0 (not and1)))))))
 (=> (and active0 active1 (and (distinct a1 (_ bv8 4)) true) (and (distinct b1 (_ bv8 4)) true)) (or (bvult a0 a1) $x402))))
(assert
 (let (($x415 (and (= a1 a2) (or (bvult b1 b2) (and (= b1 b2) (or and1 (not and2)))))))
 (=> (and active1 active2 (and (distinct a2 (_ bv9 4)) true) (and (distinct b2 (_ bv9 4)) true)) (or (bvult a1 a2) $x415))))
(assert
 (let (($x428 (and (= a2 a3) (or (bvult b2 b3) (and (= b2 b3) (or and2 (not and3)))))))
 (let (($x429 (or (bvult a2 a3) $x428)))
 (let (($x420 (and active2 active3 (and (distinct a3 (_ bv10 4)) true) (and (distinct b3 (_ bv10 4)) true))))
 (=> $x420 $x429)))))
(assert
 (let (($x436 (= b0 (_ bv7 4))))
 (let (($x90 (= a0 (_ bv5 4))))
 (let (($x448 (and $x90 $x436)))
 (let (($x109 (= b0 (_ bv6 4))))
 (let (($x447 (and $x90 $x109)))
 (let (($x72 (= a0 (_ bv4 4))))
 (let (($x446 (and $x72 $x436)))
 (let (($x91 (= b0 (_ bv5 4))))
 (let (($x445 (and $x72 $x91)))
 (let (($x54 (= a0 (_ bv3 4))))
 (let (($x444 (and $x54 $x436)))
 (let (($x443 (and $x54 $x91)))
 (let (($x73 (= b0 (_ bv4 4))))
 (let (($x442 (and $x54 $x73)))
 (let (($x36 (= a0 (_ bv2 4))))
 (let (($x441 (and $x36 $x436)))
 (let (($x440 (and $x36 $x91)))
 (let (($x439 (and $x36 $x73)))
 (let (($x55 (= b0 (_ bv3 4))))
 (let (($x438 (and $x36 $x55)))
 (let (($x151 (= a0 (_ bv0 4))))
 (let (($x437 (and $x151 $x436)))
 (let (($x435 (and $x151 $x91)))
 (let (($x434 (and $x151 $x73)))
 (let (($x433 (and $x151 $x55)))
 (let (($x37 (= b0 (_ bv2 4))))
 (let (($x432 (and $x151 $x37)))
 (let (($x158 (= b0 (_ bv1 4))))
 (let (($x431 (and $x151 $x158)))
 (or $x431 $x432 $x433 $x434 $x435 $x437 $x438 $x439 $x440 $x441 $x442 $x443 $x444 $x445 $x446 $x447 $x448)))))))))))))))))))))))))))))))
(assert
 (= w3 (_ bv270720 27)))
(check-sat)
