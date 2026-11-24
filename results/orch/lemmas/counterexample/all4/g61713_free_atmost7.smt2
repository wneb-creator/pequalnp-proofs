; benchmark generated from python API
(set-info :status unknown)
(declare-fun active0 () Bool)
(declare-fun b0 () (_ BitVec 4))
(declare-fun a0 () (_ BitVec 4))
(declare-fun and0 () Bool)
(declare-fun w0 () (_ BitVec 27))
(declare-fun b6 () (_ BitVec 4))
(declare-fun a6 () (_ BitVec 4))
(declare-fun active6 () Bool)
(declare-fun b5 () (_ BitVec 4))
(declare-fun a5 () (_ BitVec 4))
(declare-fun active5 () Bool)
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
(declare-fun and5 () Bool)
(declare-fun w5 () (_ BitVec 27))
(declare-fun and6 () Bool)
(declare-fun w6 () (_ BitVec 27))
(assert
 active0)
(assert
 (bvult b0 (_ bv8 4)))
(assert
 (=> active0 (bvult a0 b0)))
(assert
 (let (($x79 (= b0 (_ bv4 4))))
 (let ((?x80 (ite $x79 (_ bv67109856 27) (ite (= b0 (_ bv5 4)) (_ bv100695040 27) (ite (= b0 (_ bv6 4)) (_ bv101679104 27) (_ bv133169152 27))))))
 (let (($x81 (= b0 (_ bv3 4))))
 (let (($x85 (= b0 (_ bv1 4))))
 (let ((?x88 (ite (= b0 (_ bv0 4)) (_ bv35719249 27) (ite $x85 (_ bv37884050 27) (ite (= b0 (_ bv2 4)) (_ bv42213652 27) (ite $x81 (_ bv17318424 27) ?x80))))))
 (let ((?x62 (ite (= a0 (_ bv4 4)) (_ bv67109856 27) (ite (= a0 (_ bv5 4)) (_ bv100695040 27) (ite (= a0 (_ bv6 4)) (_ bv101679104 27) (_ bv133169152 27))))))
 (let (($x64 (= a0 (_ bv3 4))))
 (let ((?x71 (ite (= a0 (_ bv1 4)) (_ bv37884050 27) (ite (= a0 (_ bv2 4)) (_ bv42213652 27) (ite $x64 (_ bv17318424 27) ?x62)))))
 (let (($x73 (= a0 (_ bv0 4))))
 (let ((?x74 (ite $x73 (_ bv35719249 27) ?x71)))
 (= w0 (ite and0 (bvand ?x74 ?x88) (bvor ?x74 ?x88))))))))))))))
(assert
 (let (($x101 (and (and (distinct (_ bv35719249 27) w0) true) (and (distinct (_ bv37884050 27) w0) true) (and (distinct (_ bv42213652 27) w0) true) (and (distinct (_ bv17318424 27) w0) true) (and (distinct (_ bv67109856 27) w0) true) (and (distinct (_ bv100695040 27) w0) true) (and (distinct (_ bv101679104 27) w0) true) (and (distinct (_ bv133169152 27) w0) true))))
 (=> active0 $x101)))
(assert
 (let (($x127 (or (and active1 (or (= a1 (_ bv8 4)) (= b1 (_ bv8 4)))) (and active2 (or (= a2 (_ bv8 4)) (= b2 (_ bv8 4)))) (and active3 (or (= a3 (_ bv8 4)) (= b3 (_ bv8 4)))) (and active4 (or (= a4 (_ bv8 4)) (= b4 (_ bv8 4)))) (and active5 (or (= a5 (_ bv8 4)) (= b5 (_ bv8 4)))) (and active6 (or (= a6 (_ bv8 4)) (= b6 (_ bv8 4)))))))
 (let (($x128 (not active1)))
 (=> active0 (or $x128 $x127)))))
(assert
 (bvult b1 (_ bv9 4)))
(assert
 (=> active1 (bvult a1 b1)))
(assert
 (=> active1 active0))
(assert
 (let (($x128 (not active1)))
 (=> $x128 (and (= a1 (_ bv8 4)) (= b1 (_ bv8 4)) (not and1)))))
(assert
 (let ((?x161 (ite (= b1 (_ bv5 4)) (_ bv100695040 27) (ite (= b1 (_ bv6 4)) (_ bv101679104 27) (ite (= b1 (_ bv7 4)) (_ bv133169152 27) w0)))))
 (let ((?x167 (ite (= b1 (_ bv2 4)) (_ bv42213652 27) (ite (= b1 (_ bv3 4)) (_ bv17318424 27) (ite (= b1 (_ bv4 4)) (_ bv67109856 27) ?x161)))))
 (let ((?x171 (ite (= b1 (_ bv0 4)) (_ bv35719249 27) (ite (= b1 (_ bv1 4)) (_ bv37884050 27) ?x167))))
 (let ((?x145 (ite (= a1 (_ bv5 4)) (_ bv100695040 27) (ite (= a1 (_ bv6 4)) (_ bv101679104 27) (ite (= a1 (_ bv7 4)) (_ bv133169152 27) w0)))))
 (let ((?x151 (ite (= a1 (_ bv2 4)) (_ bv42213652 27) (ite (= a1 (_ bv3 4)) (_ bv17318424 27) (ite (= a1 (_ bv4 4)) (_ bv67109856 27) ?x145)))))
 (let ((?x155 (ite (= a1 (_ bv0 4)) (_ bv35719249 27) (ite (= a1 (_ bv1 4)) (_ bv37884050 27) ?x151))))
 (= w1 (ite and1 (bvand ?x155 ?x171) (bvor ?x155 ?x171))))))))))
(assert
 (let (($x185 (and (and (distinct (_ bv35719249 27) w1) true) (and (distinct (_ bv37884050 27) w1) true) (and (distinct (_ bv42213652 27) w1) true) (and (distinct (_ bv17318424 27) w1) true) (and (distinct (_ bv67109856 27) w1) true) (and (distinct (_ bv100695040 27) w1) true) (and (distinct (_ bv101679104 27) w1) true) (and (distinct (_ bv133169152 27) w1) true) (and (distinct w1 w0) true))))
 (=> active1 $x185)))
(assert
 (let (($x207 (or (and active2 (or (= a2 (_ bv9 4)) (= b2 (_ bv9 4)))) (and active3 (or (= a3 (_ bv9 4)) (= b3 (_ bv9 4)))) (and active4 (or (= a4 (_ bv9 4)) (= b4 (_ bv9 4)))) (and active5 (or (= a5 (_ bv9 4)) (= b5 (_ bv9 4)))) (and active6 (or (= a6 (_ bv9 4)) (= b6 (_ bv9 4)))))))
 (let (($x208 (not active2)))
 (=> active1 (or $x208 $x207)))))
(assert
 (bvult b2 (_ bv10 4)))
(assert
 (=> active2 (bvult a2 b2)))
(assert
 (=> active2 active1))
(assert
 (let (($x208 (not active2)))
 (=> $x208 (and (= a2 (_ bv9 4)) (= b2 (_ bv9 4)) (not and2)))))
(assert
 (let ((?x240 (ite (= b2 (_ bv6 4)) (_ bv101679104 27) (ite (= b2 (_ bv7 4)) (_ bv133169152 27) (ite (= b2 (_ bv8 4)) w0 w1)))))
 (let ((?x246 (ite (= b2 (_ bv3 4)) (_ bv17318424 27) (ite (= b2 (_ bv4 4)) (_ bv67109856 27) (ite (= b2 (_ bv5 4)) (_ bv100695040 27) ?x240)))))
 (let ((?x252 (ite (= b2 (_ bv0 4)) (_ bv35719249 27) (ite (= b2 (_ bv1 4)) (_ bv37884050 27) (ite (= b2 (_ bv2 4)) (_ bv42213652 27) ?x246)))))
 (let ((?x223 (ite (= a2 (_ bv6 4)) (_ bv101679104 27) (ite (= a2 (_ bv7 4)) (_ bv133169152 27) (ite (= a2 (_ bv8 4)) w0 w1)))))
 (let ((?x229 (ite (= a2 (_ bv3 4)) (_ bv17318424 27) (ite (= a2 (_ bv4 4)) (_ bv67109856 27) (ite (= a2 (_ bv5 4)) (_ bv100695040 27) ?x223)))))
 (let ((?x235 (ite (= a2 (_ bv0 4)) (_ bv35719249 27) (ite (= a2 (_ bv1 4)) (_ bv37884050 27) (ite (= a2 (_ bv2 4)) (_ bv42213652 27) ?x229)))))
 (= w2 (ite and2 (bvand ?x235 ?x252) (bvor ?x235 ?x252))))))))))
(assert
 (let (($x267 (and (and (distinct (_ bv35719249 27) w2) true) (and (distinct (_ bv37884050 27) w2) true) (and (distinct (_ bv42213652 27) w2) true) (and (distinct (_ bv17318424 27) w2) true) (and (distinct (_ bv67109856 27) w2) true) (and (distinct (_ bv100695040 27) w2) true) (and (distinct (_ bv101679104 27) w2) true) (and (distinct (_ bv133169152 27) w2) true) (and (distinct w2 w0) true) (and (distinct w2 w1) true))))
 (=> active2 $x267)))
(assert
 (let (($x285 (or (and active3 (or (= a3 (_ bv10 4)) (= b3 (_ bv10 4)))) (and active4 (or (= a4 (_ bv10 4)) (= b4 (_ bv10 4)))) (and active5 (or (= a5 (_ bv10 4)) (= b5 (_ bv10 4)))) (and active6 (or (= a6 (_ bv10 4)) (= b6 (_ bv10 4)))))))
 (let (($x286 (not active3)))
 (=> active2 (or $x286 $x285)))))
(assert
 (bvult b3 (_ bv11 4)))
(assert
 (=> active3 (bvult a3 b3)))
(assert
 (=> active3 active2))
(assert
 (let (($x286 (not active3)))
 (=> $x286 (and (= a3 (_ bv10 4)) (= b3 (_ bv10 4)) (not and3)))))
(assert
 (let ((?x318 (ite (= b3 (_ bv7 4)) (_ bv133169152 27) (ite (= b3 (_ bv8 4)) w0 (ite (= b3 (_ bv9 4)) w1 w2)))))
 (let ((?x324 (ite (= b3 (_ bv4 4)) (_ bv67109856 27) (ite (= b3 (_ bv5 4)) (_ bv100695040 27) (ite (= b3 (_ bv6 4)) (_ bv101679104 27) ?x318)))))
 (let ((?x330 (ite (= b3 (_ bv1 4)) (_ bv37884050 27) (ite (= b3 (_ bv2 4)) (_ bv42213652 27) (ite (= b3 (_ bv3 4)) (_ bv17318424 27) ?x324)))))
 (let ((?x332 (ite (= b3 (_ bv0 4)) (_ bv35719249 27) ?x330)))
 (let ((?x300 (ite (= a3 (_ bv7 4)) (_ bv133169152 27) (ite (= a3 (_ bv8 4)) w0 (ite (= a3 (_ bv9 4)) w1 w2)))))
 (let ((?x306 (ite (= a3 (_ bv4 4)) (_ bv67109856 27) (ite (= a3 (_ bv5 4)) (_ bv100695040 27) (ite (= a3 (_ bv6 4)) (_ bv101679104 27) ?x300)))))
 (let ((?x312 (ite (= a3 (_ bv1 4)) (_ bv37884050 27) (ite (= a3 (_ bv2 4)) (_ bv42213652 27) (ite (= a3 (_ bv3 4)) (_ bv17318424 27) ?x306)))))
 (let ((?x314 (ite (= a3 (_ bv0 4)) (_ bv35719249 27) ?x312)))
 (= w3 (ite and3 (bvand ?x314 ?x332) (bvor ?x314 ?x332))))))))))))
(assert
 (let (($x348 (and (and (distinct (_ bv35719249 27) w3) true) (and (distinct (_ bv37884050 27) w3) true) (and (distinct (_ bv42213652 27) w3) true) (and (distinct (_ bv17318424 27) w3) true) (and (distinct (_ bv67109856 27) w3) true) (and (distinct (_ bv100695040 27) w3) true) (and (distinct (_ bv101679104 27) w3) true) (and (distinct (_ bv133169152 27) w3) true) (and (distinct w3 w0) true) (and (distinct w3 w1) true) (and (distinct w3 w2) true))))
 (=> active3 $x348)))
(assert
 (let (($x362 (or (and active4 (or (= a4 (_ bv11 4)) (= b4 (_ bv11 4)))) (and active5 (or (= a5 (_ bv11 4)) (= b5 (_ bv11 4)))) (and active6 (or (= a6 (_ bv11 4)) (= b6 (_ bv11 4)))))))
 (let (($x363 (not active4)))
 (=> active3 (or $x363 $x362)))))
(assert
 (bvult b4 (_ bv12 4)))
(assert
 (=> active4 (bvult a4 b4)))
(assert
 (=> active4 active3))
(assert
 (let (($x363 (not active4)))
 (=> $x363 (and (= a4 (_ bv11 4)) (= b4 (_ bv11 4)) (not and4)))))
(assert
 (let (($x116 (= b4 (_ bv8 4))))
 (let ((?x395 (ite $x116 w0 (ite (= b4 (_ bv9 4)) w1 (ite (= b4 (_ bv10 4)) w2 w3)))))
 (let ((?x401 (ite (= b4 (_ bv5 4)) (_ bv100695040 27) (ite (= b4 (_ bv6 4)) (_ bv101679104 27) (ite (= b4 (_ bv7 4)) (_ bv133169152 27) ?x395)))))
 (let ((?x407 (ite (= b4 (_ bv2 4)) (_ bv42213652 27) (ite (= b4 (_ bv3 4)) (_ bv17318424 27) (ite (= b4 (_ bv4 4)) (_ bv67109856 27) ?x401)))))
 (let ((?x411 (ite (= b4 (_ bv0 4)) (_ bv35719249 27) (ite (= b4 (_ bv1 4)) (_ bv37884050 27) ?x407))))
 (let (($x115 (= a4 (_ bv8 4))))
 (let ((?x376 (ite $x115 w0 (ite (= a4 (_ bv9 4)) w1 (ite (= a4 (_ bv10 4)) w2 w3)))))
 (let ((?x382 (ite (= a4 (_ bv5 4)) (_ bv100695040 27) (ite (= a4 (_ bv6 4)) (_ bv101679104 27) (ite (= a4 (_ bv7 4)) (_ bv133169152 27) ?x376)))))
 (let ((?x388 (ite (= a4 (_ bv2 4)) (_ bv42213652 27) (ite (= a4 (_ bv3 4)) (_ bv17318424 27) (ite (= a4 (_ bv4 4)) (_ bv67109856 27) ?x382)))))
 (let ((?x392 (ite (= a4 (_ bv0 4)) (_ bv35719249 27) (ite (= a4 (_ bv1 4)) (_ bv37884050 27) ?x388))))
 (= w4 (ite and4 (bvand ?x392 ?x411) (bvor ?x392 ?x411))))))))))))))
(assert
 (let (($x428 (and (and (distinct (_ bv35719249 27) w4) true) (and (distinct (_ bv37884050 27) w4) true) (and (distinct (_ bv42213652 27) w4) true) (and (distinct (_ bv17318424 27) w4) true) (and (distinct (_ bv67109856 27) w4) true) (and (distinct (_ bv100695040 27) w4) true) (and (distinct (_ bv101679104 27) w4) true) (and (distinct (_ bv133169152 27) w4) true) (and (distinct w4 w0) true) (and (distinct w4 w1) true) (and (distinct w4 w2) true) (and (distinct w4 w3) true))))
 (=> active4 $x428)))
(assert
 (let (($x438 (or (and active5 (or (= a5 (_ bv12 4)) (= b5 (_ bv12 4)))) (and active6 (or (= a6 (_ bv12 4)) (= b6 (_ bv12 4)))))))
 (let (($x439 (not active5)))
 (=> active4 (or $x439 $x438)))))
(assert
 (bvult b5 (_ bv13 4)))
(assert
 (=> active5 (bvult a5 b5)))
(assert
 (=> active5 active4))
(assert
 (let (($x439 (not active5)))
 (=> $x439 (and (= a5 (_ bv12 4)) (= b5 (_ bv12 4)) (not and5)))))
(assert
 (let (($x200 (= b5 (_ bv9 4))))
 (let ((?x472 (ite $x200 w1 (ite (= b5 (_ bv10 4)) w2 (ite (= b5 (_ bv11 4)) w3 w4)))))
 (let (($x120 (= b5 (_ bv8 4))))
 (let ((?x477 (ite (= b5 (_ bv6 4)) (_ bv101679104 27) (ite (= b5 (_ bv7 4)) (_ bv133169152 27) (ite $x120 w0 ?x472)))))
 (let ((?x483 (ite (= b5 (_ bv3 4)) (_ bv17318424 27) (ite (= b5 (_ bv4 4)) (_ bv67109856 27) (ite (= b5 (_ bv5 4)) (_ bv100695040 27) ?x477)))))
 (let ((?x489 (ite (= b5 (_ bv0 4)) (_ bv35719249 27) (ite (= b5 (_ bv1 4)) (_ bv37884050 27) (ite (= b5 (_ bv2 4)) (_ bv42213652 27) ?x483)))))
 (let (($x199 (= a5 (_ bv9 4))))
 (let ((?x452 (ite $x199 w1 (ite (= a5 (_ bv10 4)) w2 (ite (= a5 (_ bv11 4)) w3 w4)))))
 (let (($x119 (= a5 (_ bv8 4))))
 (let ((?x457 (ite (= a5 (_ bv6 4)) (_ bv101679104 27) (ite (= a5 (_ bv7 4)) (_ bv133169152 27) (ite $x119 w0 ?x452)))))
 (let ((?x463 (ite (= a5 (_ bv3 4)) (_ bv17318424 27) (ite (= a5 (_ bv4 4)) (_ bv67109856 27) (ite (= a5 (_ bv5 4)) (_ bv100695040 27) ?x457)))))
 (let ((?x469 (ite (= a5 (_ bv0 4)) (_ bv35719249 27) (ite (= a5 (_ bv1 4)) (_ bv37884050 27) (ite (= a5 (_ bv2 4)) (_ bv42213652 27) ?x463)))))
 (= w5 (ite and5 (bvand ?x469 ?x489) (bvor ?x469 ?x489))))))))))))))))
(assert
 (let (($x507 (and (and (distinct (_ bv35719249 27) w5) true) (and (distinct (_ bv37884050 27) w5) true) (and (distinct (_ bv42213652 27) w5) true) (and (distinct (_ bv17318424 27) w5) true) (and (distinct (_ bv67109856 27) w5) true) (and (distinct (_ bv100695040 27) w5) true) (and (distinct (_ bv101679104 27) w5) true) (and (distinct (_ bv133169152 27) w5) true) (and (distinct w5 w0) true) (and (distinct w5 w1) true) (and (distinct w5 w2) true) (and (distinct w5 w3) true) (and (distinct w5 w4) true))))
 (=> active5 $x507)))
(assert
 (let (($x513 (or (and active6 (or (= a6 (_ bv13 4)) (= b6 (_ bv13 4)))))))
 (let (($x514 (not active6)))
 (=> active5 (or $x514 $x513)))))
(assert
 (bvult b6 (_ bv14 4)))
(assert
 (=> active6 (bvult a6 b6)))
(assert
 (=> active6 active5))
(assert
 (let (($x514 (not active6)))
 (=> $x514 (and (= a6 (_ bv13 4)) (= b6 (_ bv13 4)) (not and6)))))
(assert
 (let (($x282 (= b6 (_ bv10 4))))
 (let ((?x548 (ite $x282 w2 (ite (= b6 (_ bv11 4)) w3 (ite (= b6 (_ bv12 4)) w4 w5)))))
 (let (($x204 (= b6 (_ bv9 4))))
 (let (($x124 (= b6 (_ bv8 4))))
 (let ((?x554 (ite (= b6 (_ bv6 4)) (_ bv101679104 27) (ite (= b6 (_ bv7 4)) (_ bv133169152 27) (ite $x124 w0 (ite $x204 w1 ?x548))))))
 (let ((?x560 (ite (= b6 (_ bv3 4)) (_ bv17318424 27) (ite (= b6 (_ bv4 4)) (_ bv67109856 27) (ite (= b6 (_ bv5 4)) (_ bv100695040 27) ?x554)))))
 (let ((?x566 (ite (= b6 (_ bv0 4)) (_ bv35719249 27) (ite (= b6 (_ bv1 4)) (_ bv37884050 27) (ite (= b6 (_ bv2 4)) (_ bv42213652 27) ?x560)))))
 (let (($x281 (= a6 (_ bv10 4))))
 (let ((?x527 (ite $x281 w2 (ite (= a6 (_ bv11 4)) w3 (ite (= a6 (_ bv12 4)) w4 w5)))))
 (let (($x203 (= a6 (_ bv9 4))))
 (let (($x123 (= a6 (_ bv8 4))))
 (let ((?x533 (ite (= a6 (_ bv6 4)) (_ bv101679104 27) (ite (= a6 (_ bv7 4)) (_ bv133169152 27) (ite $x123 w0 (ite $x203 w1 ?x527))))))
 (let ((?x539 (ite (= a6 (_ bv3 4)) (_ bv17318424 27) (ite (= a6 (_ bv4 4)) (_ bv67109856 27) (ite (= a6 (_ bv5 4)) (_ bv100695040 27) ?x533)))))
 (let ((?x545 (ite (= a6 (_ bv0 4)) (_ bv35719249 27) (ite (= a6 (_ bv1 4)) (_ bv37884050 27) (ite (= a6 (_ bv2 4)) (_ bv42213652 27) ?x539)))))
 (= w6 (ite and6 (bvand ?x545 ?x566) (bvor ?x545 ?x566))))))))))))))))))
(assert
 (let (($x585 (and (and (distinct (_ bv35719249 27) w6) true) (and (distinct (_ bv37884050 27) w6) true) (and (distinct (_ bv42213652 27) w6) true) (and (distinct (_ bv17318424 27) w6) true) (and (distinct (_ bv67109856 27) w6) true) (and (distinct (_ bv100695040 27) w6) true) (and (distinct (_ bv101679104 27) w6) true) (and (distinct (_ bv133169152 27) w6) true) (and (distinct w6 w0) true) (and (distinct w6 w1) true) (and (distinct w6 w2) true) (and (distinct w6 w3) true) (and (distinct w6 w4) true) (and (distinct w6 w5) true))))
 (=> active6 $x585)))
(assert
 (let (($x597 (and (= a0 a1) (or (bvult b0 b1) (and (= b0 b1) (or and0 (not and1)))))))
 (=> (and active0 active1 (and (distinct a1 (_ bv8 4)) true) (and (distinct b1 (_ bv8 4)) true)) (or (bvult a0 a1) $x597))))
(assert
 (let (($x610 (and (= a1 a2) (or (bvult b1 b2) (and (= b1 b2) (or and1 (not and2)))))))
 (=> (and active1 active2 (and (distinct a2 (_ bv9 4)) true) (and (distinct b2 (_ bv9 4)) true)) (or (bvult a1 a2) $x610))))
(assert
 (let (($x623 (and (= a2 a3) (or (bvult b2 b3) (and (= b2 b3) (or and2 (not and3)))))))
 (=> (and active2 active3 (and (distinct a3 (_ bv10 4)) true) (and (distinct b3 (_ bv10 4)) true)) (or (bvult a2 a3) $x623))))
(assert
 (let (($x636 (and (= a3 a4) (or (bvult b3 b4) (and (= b3 b4) (or and3 (not and4)))))))
 (=> (and active3 active4 (and (distinct a4 (_ bv11 4)) true) (and (distinct b4 (_ bv11 4)) true)) (or (bvult a3 a4) $x636))))
(assert
 (let (($x649 (and (= a4 a5) (or (bvult b4 b5) (and (= b4 b5) (or and4 (not and5)))))))
 (=> (and active4 active5 (and (distinct a5 (_ bv12 4)) true) (and (distinct b5 (_ bv12 4)) true)) (or (bvult a4 a5) $x649))))
(assert
 (let (($x662 (and (= a5 a6) (or (bvult b5 b6) (and (= b5 b6) (or and5 (not and6)))))))
 (let (($x663 (or (bvult a5 a6) $x662)))
 (let (($x654 (and active5 active6 (and (distinct a6 (_ bv13 4)) true) (and (distinct b6 (_ bv13 4)) true))))
 (=> $x654 $x663)))))
(assert
 (let (($x79 (= b0 (_ bv4 4))))
 (let (($x64 (= a0 (_ bv3 4))))
 (let (($x669 (and $x64 $x79)))
 (let (($x77 (= b0 (_ bv5 4))))
 (let (($x73 (= a0 (_ bv0 4))))
 (let (($x668 (and $x73 $x77)))
 (let (($x667 (and $x73 $x79)))
 (let (($x81 (= b0 (_ bv3 4))))
 (let (($x666 (and $x73 $x81)))
 (let (($x85 (= b0 (_ bv1 4))))
 (let (($x665 (and $x73 $x85)))
 (or $x665 $x666 $x667 $x668 $x669)))))))))))))
(assert
 (= w6 (_ bv17318848 27)))
(check-sat)
