; benchmark generated from python API
(set-info :status unknown)
(declare-fun active0 () Bool)
(declare-fun active4 () Bool)
(declare-fun b5 () (_ BitVec 4))
(declare-fun a5 () (_ BitVec 4))
(declare-fun active5 () Bool)
(declare-fun b4 () (_ BitVec 4))
(declare-fun a4 () (_ BitVec 4))
(declare-fun b3 () (_ BitVec 4))
(declare-fun a3 () (_ BitVec 4))
(declare-fun active3 () Bool)
(declare-fun b2 () (_ BitVec 4))
(declare-fun a2 () (_ BitVec 4))
(declare-fun active2 () Bool)
(declare-fun b1 () (_ BitVec 4))
(declare-fun a1 () (_ BitVec 4))
(declare-fun active1 () Bool)
(declare-fun b0 () (_ BitVec 4))
(declare-fun a0 () (_ BitVec 4))
(declare-fun and0 () Bool)
(declare-fun w0 () (_ BitVec 29))
(declare-fun and1 () Bool)
(declare-fun w1 () (_ BitVec 29))
(declare-fun and2 () Bool)
(declare-fun w2 () (_ BitVec 29))
(declare-fun and3 () Bool)
(declare-fun w3 () (_ BitVec 29))
(declare-fun and4 () Bool)
(declare-fun w4 () (_ BitVec 29))
(declare-fun and5 () Bool)
(declare-fun w5 () (_ BitVec 29))
(assert
 active0)
(assert
 active4)
(assert
 (or (and active0 (or (= a0 (_ bv1 4)) (= b0 (_ bv1 4)))) (and active1 (or (= a1 (_ bv1 4)) (= b1 (_ bv1 4)))) (and active2 (or (= a2 (_ bv1 4)) (= b2 (_ bv1 4)))) (and active3 (or (= a3 (_ bv1 4)) (= b3 (_ bv1 4)))) (and active4 (or (= a4 (_ bv1 4)) (= b4 (_ bv1 4)))) (and active5 (or (= a5 (_ bv1 4)) (= b5 (_ bv1 4))))))
(assert
 (or (and active0 (or (= a0 (_ bv2 4)) (= b0 (_ bv2 4)))) (and active1 (or (= a1 (_ bv2 4)) (= b1 (_ bv2 4)))) (and active2 (or (= a2 (_ bv2 4)) (= b2 (_ bv2 4)))) (and active3 (or (= a3 (_ bv2 4)) (= b3 (_ bv2 4)))) (and active4 (or (= a4 (_ bv2 4)) (= b4 (_ bv2 4)))) (and active5 (or (= a5 (_ bv2 4)) (= b5 (_ bv2 4))))))
(assert
 (or (and active0 (or (= a0 (_ bv3 4)) (= b0 (_ bv3 4)))) (and active1 (or (= a1 (_ bv3 4)) (= b1 (_ bv3 4)))) (and active2 (or (= a2 (_ bv3 4)) (= b2 (_ bv3 4)))) (and active3 (or (= a3 (_ bv3 4)) (= b3 (_ bv3 4)))) (and active4 (or (= a4 (_ bv3 4)) (= b4 (_ bv3 4)))) (and active5 (or (= a5 (_ bv3 4)) (= b5 (_ bv3 4))))))
(assert
 (or (and active0 (or (= a0 (_ bv4 4)) (= b0 (_ bv4 4)))) (and active1 (or (= a1 (_ bv4 4)) (= b1 (_ bv4 4)))) (and active2 (or (= a2 (_ bv4 4)) (= b2 (_ bv4 4)))) (and active3 (or (= a3 (_ bv4 4)) (= b3 (_ bv4 4)))) (and active4 (or (= a4 (_ bv4 4)) (= b4 (_ bv4 4)))) (and active5 (or (= a5 (_ bv4 4)) (= b5 (_ bv4 4))))))
(assert
 (or (and active0 (or (= a0 (_ bv5 4)) (= b0 (_ bv5 4)))) (and active1 (or (= a1 (_ bv5 4)) (= b1 (_ bv5 4)))) (and active2 (or (= a2 (_ bv5 4)) (= b2 (_ bv5 4)))) (and active3 (or (= a3 (_ bv5 4)) (= b3 (_ bv5 4)))) (and active4 (or (= a4 (_ bv5 4)) (= b4 (_ bv5 4)))) (and active5 (or (= a5 (_ bv5 4)) (= b5 (_ bv5 4))))))
(assert
 (or (and active0 (or (= a0 (_ bv6 4)) (= b0 (_ bv6 4)))) (and active1 (or (= a1 (_ bv6 4)) (= b1 (_ bv6 4)))) (and active2 (or (= a2 (_ bv6 4)) (= b2 (_ bv6 4)))) (and active3 (or (= a3 (_ bv6 4)) (= b3 (_ bv6 4)))) (and active4 (or (= a4 (_ bv6 4)) (= b4 (_ bv6 4)))) (and active5 (or (= a5 (_ bv6 4)) (= b5 (_ bv6 4))))))
(assert
 (bvult b0 (_ bv8 4)))
(assert
 (=> active0 (bvult a0 b0)))
(assert
 (=> active0 (and (and (distinct a0 (_ bv0 4)) true) (and (distinct b0 (_ bv0 4)) true))))
(assert
 (=> active0 (and (and (distinct a0 (_ bv7 4)) true) (and (distinct b0 (_ bv7 4)) true))))
(assert
 (let (($x125 (= b0 (_ bv4 4))))
 (let ((?x225 (ite $x125 (_ bv301990384 29) (ite (= b0 (_ bv5 4)) (_ bv402669056 29) (ite (= b0 (_ bv6 4)) (_ bv470269952 29) (_ bv536346624 29))))))
 (let (($x99 (= b0 (_ bv3 4))))
 (let (($x73 (= b0 (_ bv2 4))))
 (let (($x47 (= b0 (_ bv1 4))))
 (let ((?x230 (ite (= b0 (_ bv0 4)) (_ bv521176097 29) (ite $x47 (_ bv220268610 29) (ite $x73 (_ bv88215684 29) (ite $x99 (_ bv58990856 29) ?x225))))))
 (let (($x124 (= a0 (_ bv4 4))))
 (let ((?x217 (ite $x124 (_ bv301990384 29) (ite (= a0 (_ bv5 4)) (_ bv402669056 29) (ite (= a0 (_ bv6 4)) (_ bv470269952 29) (_ bv536346624 29))))))
 (let (($x98 (= a0 (_ bv3 4))))
 (let (($x72 (= a0 (_ bv2 4))))
 (let (($x46 (= a0 (_ bv1 4))))
 (let (($x221 (= a0 (_ bv0 4))))
 (let ((?x222 (ite $x221 (_ bv521176097 29) (ite $x46 (_ bv220268610 29) (ite $x72 (_ bv88215684 29) (ite $x98 (_ bv58990856 29) ?x217))))))
 (= w0 (ite and0 (bvand ?x222 ?x230) (bvor ?x222 ?x230)))))))))))))))))
(assert
 (let (($x243 (and (and (distinct (_ bv521176097 29) w0) true) (and (distinct (_ bv220268610 29) w0) true) (and (distinct (_ bv88215684 29) w0) true) (and (distinct (_ bv58990856 29) w0) true) (and (distinct (_ bv301990384 29) w0) true) (and (distinct (_ bv402669056 29) w0) true) (and (distinct (_ bv470269952 29) w0) true) (and (distinct (_ bv536346624 29) w0) true))))
 (=> active0 $x243)))
(assert
 (let (($x265 (or (and active1 (or (= a1 (_ bv8 4)) (= b1 (_ bv8 4)))) (and active2 (or (= a2 (_ bv8 4)) (= b2 (_ bv8 4)))) (and active3 (or (= a3 (_ bv8 4)) (= b3 (_ bv8 4)))) (and active4 (or (= a4 (_ bv8 4)) (= b4 (_ bv8 4)))) (and active5 (or (= a5 (_ bv8 4)) (= b5 (_ bv8 4)))))))
 (let (($x266 (not active1)))
 (=> active0 (or $x266 $x265)))))
(assert
 (bvult b1 (_ bv9 4)))
(assert
 (=> active1 (bvult a1 b1)))
(assert
 (=> active1 (and (and (distinct a1 (_ bv0 4)) true) (and (distinct b1 (_ bv0 4)) true))))
(assert
 (=> active1 (and (and (distinct a1 (_ bv7 4)) true) (and (distinct b1 (_ bv7 4)) true))))
(assert
 (=> active1 active0))
(assert
 (let (($x266 (not active1)))
 (=> $x266 (and (= a1 (_ bv8 4)) (= b1 (_ bv8 4)) (not and1)))))
(assert
 (let (($x155 (= b1 (_ bv5 4))))
 (let ((?x298 (ite $x155 (_ bv402669056 29) (ite (= b1 (_ bv6 4)) (_ bv470269952 29) (ite (= b1 (_ bv7 4)) (_ bv536346624 29) w0)))))
 (let (($x129 (= b1 (_ bv4 4))))
 (let (($x103 (= b1 (_ bv3 4))))
 (let (($x77 (= b1 (_ bv2 4))))
 (let (($x51 (= b1 (_ bv1 4))))
 (let ((?x304 (ite (= b1 (_ bv0 4)) (_ bv521176097 29) (ite $x51 (_ bv220268610 29) (ite $x77 (_ bv88215684 29) (ite $x103 (_ bv58990856 29) (ite $x129 (_ bv301990384 29) ?x298)))))))
 (let (($x154 (= a1 (_ bv5 4))))
 (let ((?x288 (ite $x154 (_ bv402669056 29) (ite (= a1 (_ bv6 4)) (_ bv470269952 29) (ite (= a1 (_ bv7 4)) (_ bv536346624 29) w0)))))
 (let (($x128 (= a1 (_ bv4 4))))
 (let (($x102 (= a1 (_ bv3 4))))
 (let (($x76 (= a1 (_ bv2 4))))
 (let (($x50 (= a1 (_ bv1 4))))
 (let ((?x294 (ite (= a1 (_ bv0 4)) (_ bv521176097 29) (ite $x50 (_ bv220268610 29) (ite $x76 (_ bv88215684 29) (ite $x102 (_ bv58990856 29) (ite $x128 (_ bv301990384 29) ?x288)))))))
 (= w1 (ite and1 (bvand ?x294 ?x304) (bvor ?x294 ?x304))))))))))))))))))
(assert
 (let (($x318 (and (and (distinct (_ bv521176097 29) w1) true) (and (distinct (_ bv220268610 29) w1) true) (and (distinct (_ bv88215684 29) w1) true) (and (distinct (_ bv58990856 29) w1) true) (and (distinct (_ bv301990384 29) w1) true) (and (distinct (_ bv402669056 29) w1) true) (and (distinct (_ bv470269952 29) w1) true) (and (distinct (_ bv536346624 29) w1) true) (and (distinct w1 w0) true))))
 (=> active1 $x318)))
(assert
 (let (($x336 (or (and active2 (or (= a2 (_ bv9 4)) (= b2 (_ bv9 4)))) (and active3 (or (= a3 (_ bv9 4)) (= b3 (_ bv9 4)))) (and active4 (or (= a4 (_ bv9 4)) (= b4 (_ bv9 4)))) (and active5 (or (= a5 (_ bv9 4)) (= b5 (_ bv9 4)))))))
 (let (($x337 (not active2)))
 (=> active1 (or $x337 $x336)))))
(assert
 (bvult b2 (_ bv10 4)))
(assert
 (=> active2 (bvult a2 b2)))
(assert
 (=> active2 (and (and (distinct a2 (_ bv0 4)) true) (and (distinct b2 (_ bv0 4)) true))))
(assert
 (=> active2 (and (and (distinct a2 (_ bv7 4)) true) (and (distinct b2 (_ bv7 4)) true))))
(assert
 (=> active2 active1))
(assert
 (let (($x337 (not active2)))
 (=> $x337 (and (= a2 (_ bv9 4)) (= b2 (_ bv9 4)) (not and2)))))
(assert
 (let (($x185 (= b2 (_ bv6 4))))
 (let ((?x370 (ite $x185 (_ bv470269952 29) (ite (= b2 (_ bv7 4)) (_ bv536346624 29) (ite (= b2 (_ bv8 4)) w0 w1)))))
 (let (($x159 (= b2 (_ bv5 4))))
 (let (($x133 (= b2 (_ bv4 4))))
 (let (($x107 (= b2 (_ bv3 4))))
 (let (($x81 (= b2 (_ bv2 4))))
 (let (($x55 (= b2 (_ bv1 4))))
 (let ((?x375 (ite $x55 (_ bv220268610 29) (ite $x81 (_ bv88215684 29) (ite $x107 (_ bv58990856 29) (ite $x133 (_ bv301990384 29) (ite $x159 (_ bv402669056 29) ?x370)))))))
 (let ((?x377 (ite (= b2 (_ bv0 4)) (_ bv521176097 29) ?x375)))
 (let (($x184 (= a2 (_ bv6 4))))
 (let ((?x359 (ite $x184 (_ bv470269952 29) (ite (= a2 (_ bv7 4)) (_ bv536346624 29) (ite (= a2 (_ bv8 4)) w0 w1)))))
 (let (($x158 (= a2 (_ bv5 4))))
 (let (($x132 (= a2 (_ bv4 4))))
 (let (($x106 (= a2 (_ bv3 4))))
 (let (($x80 (= a2 (_ bv2 4))))
 (let (($x54 (= a2 (_ bv1 4))))
 (let ((?x364 (ite $x54 (_ bv220268610 29) (ite $x80 (_ bv88215684 29) (ite $x106 (_ bv58990856 29) (ite $x132 (_ bv301990384 29) (ite $x158 (_ bv402669056 29) ?x359)))))))
 (let ((?x366 (ite (= a2 (_ bv0 4)) (_ bv521176097 29) ?x364)))
 (= w2 (ite and2 (bvand ?x366 ?x377) (bvor ?x366 ?x377))))))))))))))))))))))
(assert
 (let (($x392 (and (and (distinct (_ bv521176097 29) w2) true) (and (distinct (_ bv220268610 29) w2) true) (and (distinct (_ bv88215684 29) w2) true) (and (distinct (_ bv58990856 29) w2) true) (and (distinct (_ bv301990384 29) w2) true) (and (distinct (_ bv402669056 29) w2) true) (and (distinct (_ bv470269952 29) w2) true) (and (distinct (_ bv536346624 29) w2) true) (and (distinct w2 w0) true) (and (distinct w2 w1) true))))
 (=> active2 $x392)))
(assert
 (let (($x406 (or (and active3 (or (= a3 (_ bv10 4)) (= b3 (_ bv10 4)))) (and active4 (or (= a4 (_ bv10 4)) (= b4 (_ bv10 4)))) (and active5 (or (= a5 (_ bv10 4)) (= b5 (_ bv10 4)))))))
 (let (($x407 (not active3)))
 (=> active2 (or $x407 $x406)))))
(assert
 (bvult b3 (_ bv11 4)))
(assert
 (=> active3 (bvult a3 b3)))
(assert
 (=> active3 (and (and (distinct a3 (_ bv0 4)) true) (and (distinct b3 (_ bv0 4)) true))))
(assert
 (=> active3 (and (and (distinct a3 (_ bv7 4)) true) (and (distinct b3 (_ bv7 4)) true))))
(assert
 (=> active3 active2))
(assert
 (let (($x407 (not active3)))
 (=> $x407 (and (= a3 (_ bv10 4)) (= b3 (_ bv10 4)) (not and3)))))
(assert
 (let ((?x441 (ite (= b3 (_ bv7 4)) (_ bv536346624 29) (ite (= b3 (_ bv8 4)) w0 (ite (= b3 (_ bv9 4)) w1 w2)))))
 (let (($x189 (= b3 (_ bv6 4))))
 (let (($x163 (= b3 (_ bv5 4))))
 (let (($x137 (= b3 (_ bv4 4))))
 (let (($x111 (= b3 (_ bv3 4))))
 (let (($x85 (= b3 (_ bv2 4))))
 (let ((?x446 (ite $x85 (_ bv88215684 29) (ite $x111 (_ bv58990856 29) (ite $x137 (_ bv301990384 29) (ite $x163 (_ bv402669056 29) (ite $x189 (_ bv470269952 29) ?x441)))))))
 (let (($x59 (= b3 (_ bv1 4))))
 (let ((?x449 (ite (= b3 (_ bv0 4)) (_ bv521176097 29) (ite $x59 (_ bv220268610 29) ?x446))))
 (let ((?x429 (ite (= a3 (_ bv7 4)) (_ bv536346624 29) (ite (= a3 (_ bv8 4)) w0 (ite (= a3 (_ bv9 4)) w1 w2)))))
 (let (($x188 (= a3 (_ bv6 4))))
 (let (($x162 (= a3 (_ bv5 4))))
 (let (($x136 (= a3 (_ bv4 4))))
 (let (($x110 (= a3 (_ bv3 4))))
 (let (($x84 (= a3 (_ bv2 4))))
 (let ((?x434 (ite $x84 (_ bv88215684 29) (ite $x110 (_ bv58990856 29) (ite $x136 (_ bv301990384 29) (ite $x162 (_ bv402669056 29) (ite $x188 (_ bv470269952 29) ?x429)))))))
 (let (($x58 (= a3 (_ bv1 4))))
 (let ((?x437 (ite (= a3 (_ bv0 4)) (_ bv521176097 29) (ite $x58 (_ bv220268610 29) ?x434))))
 (= w3 (ite and3 (bvand ?x437 ?x449) (bvor ?x437 ?x449))))))))))))))))))))))
(assert
 (let (($x465 (and (and (distinct (_ bv521176097 29) w3) true) (and (distinct (_ bv220268610 29) w3) true) (and (distinct (_ bv88215684 29) w3) true) (and (distinct (_ bv58990856 29) w3) true) (and (distinct (_ bv301990384 29) w3) true) (and (distinct (_ bv402669056 29) w3) true) (and (distinct (_ bv470269952 29) w3) true) (and (distinct (_ bv536346624 29) w3) true) (and (distinct w3 w0) true) (and (distinct w3 w1) true) (and (distinct w3 w2) true))))
 (=> active3 $x465)))
(assert
 (let (($x475 (or (and active4 (or (= a4 (_ bv11 4)) (= b4 (_ bv11 4)))) (and active5 (or (= a5 (_ bv11 4)) (= b5 (_ bv11 4)))))))
 (let (($x476 (not active4)))
 (=> active3 (or $x476 $x475)))))
(assert
 (bvult b4 (_ bv12 4)))
(assert
 (=> active4 (bvult a4 b4)))
(assert
 (=> active4 (and (and (distinct a4 (_ bv0 4)) true) (and (distinct b4 (_ bv0 4)) true))))
(assert
 (=> active4 (and (and (distinct a4 (_ bv7 4)) true) (and (distinct b4 (_ bv7 4)) true))))
(assert
 (=> active4 active3))
(assert
 (let (($x476 (not active4)))
 (=> $x476 (and (= a4 (_ bv11 4)) (= b4 (_ bv11 4)) (not and4)))))
(assert
 (let (($x258 (= b4 (_ bv8 4))))
 (let ((?x510 (ite $x258 w0 (ite (= b4 (_ bv9 4)) w1 (ite (= b4 (_ bv10 4)) w2 w3)))))
 (let (($x193 (= b4 (_ bv6 4))))
 (let (($x167 (= b4 (_ bv5 4))))
 (let (($x141 (= b4 (_ bv4 4))))
 (let ((?x515 (ite $x141 (_ bv301990384 29) (ite $x167 (_ bv402669056 29) (ite $x193 (_ bv470269952 29) (ite (= b4 (_ bv7 4)) (_ bv536346624 29) ?x510))))))
 (let (($x115 (= b4 (_ bv3 4))))
 (let (($x89 (= b4 (_ bv2 4))))
 (let (($x63 (= b4 (_ bv1 4))))
 (let ((?x520 (ite (= b4 (_ bv0 4)) (_ bv521176097 29) (ite $x63 (_ bv220268610 29) (ite $x89 (_ bv88215684 29) (ite $x115 (_ bv58990856 29) ?x515))))))
 (let (($x257 (= a4 (_ bv8 4))))
 (let ((?x497 (ite $x257 w0 (ite (= a4 (_ bv9 4)) w1 (ite (= a4 (_ bv10 4)) w2 w3)))))
 (let (($x192 (= a4 (_ bv6 4))))
 (let (($x166 (= a4 (_ bv5 4))))
 (let (($x140 (= a4 (_ bv4 4))))
 (let ((?x502 (ite $x140 (_ bv301990384 29) (ite $x166 (_ bv402669056 29) (ite $x192 (_ bv470269952 29) (ite (= a4 (_ bv7 4)) (_ bv536346624 29) ?x497))))))
 (let (($x114 (= a4 (_ bv3 4))))
 (let (($x88 (= a4 (_ bv2 4))))
 (let (($x62 (= a4 (_ bv1 4))))
 (let ((?x507 (ite (= a4 (_ bv0 4)) (_ bv521176097 29) (ite $x62 (_ bv220268610 29) (ite $x88 (_ bv88215684 29) (ite $x114 (_ bv58990856 29) ?x502))))))
 (= w4 (ite and4 (bvand ?x507 ?x520) (bvor ?x507 ?x520))))))))))))))))))))))))
(assert
 (let (($x537 (and (and (distinct (_ bv521176097 29) w4) true) (and (distinct (_ bv220268610 29) w4) true) (and (distinct (_ bv88215684 29) w4) true) (and (distinct (_ bv58990856 29) w4) true) (and (distinct (_ bv301990384 29) w4) true) (and (distinct (_ bv402669056 29) w4) true) (and (distinct (_ bv470269952 29) w4) true) (and (distinct (_ bv536346624 29) w4) true) (and (distinct w4 w0) true) (and (distinct w4 w1) true) (and (distinct w4 w2) true) (and (distinct w4 w3) true))))
 (=> active4 $x537)))
(assert
 (let (($x543 (or (and active5 (or (= a5 (_ bv12 4)) (= b5 (_ bv12 4)))))))
 (let (($x544 (not active5)))
 (=> active4 (or $x544 $x543)))))
(assert
 (bvult b5 (_ bv13 4)))
(assert
 (=> active5 (bvult a5 b5)))
(assert
 (=> active5 (and (and (distinct a5 (_ bv0 4)) true) (and (distinct b5 (_ bv0 4)) true))))
(assert
 (=> active5 (and (and (distinct a5 (_ bv7 4)) true) (and (distinct b5 (_ bv7 4)) true))))
(assert
 (=> active5 active4))
(assert
 (let (($x544 (not active5)))
 (=> $x544 (and (= a5 (_ bv12 4)) (= b5 (_ bv12 4)) (not and5)))))
(assert
 (let (($x333 (= b5 (_ bv9 4))))
 (let ((?x579 (ite $x333 w1 (ite (= b5 (_ bv10 4)) w2 (ite (= b5 (_ bv11 4)) w3 w4)))))
 (let (($x262 (= b5 (_ bv8 4))))
 (let (($x197 (= b5 (_ bv6 4))))
 (let (($x171 (= b5 (_ bv5 4))))
 (let ((?x584 (ite $x171 (_ bv402669056 29) (ite $x197 (_ bv470269952 29) (ite (= b5 (_ bv7 4)) (_ bv536346624 29) (ite $x262 w0 ?x579))))))
 (let (($x145 (= b5 (_ bv4 4))))
 (let (($x119 (= b5 (_ bv3 4))))
 (let (($x93 (= b5 (_ bv2 4))))
 (let (($x67 (= b5 (_ bv1 4))))
 (let ((?x590 (ite (= b5 (_ bv0 4)) (_ bv521176097 29) (ite $x67 (_ bv220268610 29) (ite $x93 (_ bv88215684 29) (ite $x119 (_ bv58990856 29) (ite $x145 (_ bv301990384 29) ?x584)))))))
 (let (($x332 (= a5 (_ bv9 4))))
 (let ((?x565 (ite $x332 w1 (ite (= a5 (_ bv10 4)) w2 (ite (= a5 (_ bv11 4)) w3 w4)))))
 (let (($x261 (= a5 (_ bv8 4))))
 (let (($x196 (= a5 (_ bv6 4))))
 (let (($x170 (= a5 (_ bv5 4))))
 (let ((?x570 (ite $x170 (_ bv402669056 29) (ite $x196 (_ bv470269952 29) (ite (= a5 (_ bv7 4)) (_ bv536346624 29) (ite $x261 w0 ?x565))))))
 (let (($x144 (= a5 (_ bv4 4))))
 (let (($x118 (= a5 (_ bv3 4))))
 (let (($x92 (= a5 (_ bv2 4))))
 (let (($x66 (= a5 (_ bv1 4))))
 (let ((?x576 (ite (= a5 (_ bv0 4)) (_ bv521176097 29) (ite $x66 (_ bv220268610 29) (ite $x92 (_ bv88215684 29) (ite $x118 (_ bv58990856 29) (ite $x144 (_ bv301990384 29) ?x570)))))))
 (= w5 (ite and5 (bvand ?x576 ?x590) (bvor ?x576 ?x590))))))))))))))))))))))))))
(assert
 (let (($x608 (and (and (distinct (_ bv521176097 29) w5) true) (and (distinct (_ bv220268610 29) w5) true) (and (distinct (_ bv88215684 29) w5) true) (and (distinct (_ bv58990856 29) w5) true) (and (distinct (_ bv301990384 29) w5) true) (and (distinct (_ bv402669056 29) w5) true) (and (distinct (_ bv470269952 29) w5) true) (and (distinct (_ bv536346624 29) w5) true) (and (distinct w5 w0) true) (and (distinct w5 w1) true) (and (distinct w5 w2) true) (and (distinct w5 w3) true) (and (distinct w5 w4) true))))
 (=> active5 $x608)))
(assert
 (let (($x620 (and (= a0 a1) (or (bvult b0 b1) (and (= b0 b1) (or and0 (not and1)))))))
 (=> (and active0 active1 (and (distinct a1 (_ bv8 4)) true) (and (distinct b1 (_ bv8 4)) true)) (or (bvult a0 a1) $x620))))
(assert
 (let (($x633 (and (= a1 a2) (or (bvult b1 b2) (and (= b1 b2) (or and1 (not and2)))))))
 (=> (and active1 active2 (and (distinct a2 (_ bv9 4)) true) (and (distinct b2 (_ bv9 4)) true)) (or (bvult a1 a2) $x633))))
(assert
 (let (($x646 (and (= a2 a3) (or (bvult b2 b3) (and (= b2 b3) (or and2 (not and3)))))))
 (=> (and active2 active3 (and (distinct a3 (_ bv10 4)) true) (and (distinct b3 (_ bv10 4)) true)) (or (bvult a2 a3) $x646))))
(assert
 (let (($x659 (and (= a3 a4) (or (bvult b3 b4) (and (= b3 b4) (or and3 (not and4)))))))
 (=> (and active3 active4 (and (distinct a4 (_ bv11 4)) true) (and (distinct b4 (_ bv11 4)) true)) (or (bvult a3 a4) $x659))))
(assert
 (let (($x672 (and (= a4 a5) (or (bvult b4 b5) (and (= b4 b5) (or and4 (not and5)))))))
 (let (($x673 (or (bvult a4 a5) $x672)))
 (let (($x664 (and active4 active5 (and (distinct a5 (_ bv12 4)) true) (and (distinct b5 (_ bv12 4)) true))))
 (=> $x664 $x673)))))
(assert
 (let (($x125 (= b0 (_ bv4 4))))
 (let (($x98 (= a0 (_ bv3 4))))
 (let (($x691 (and $x98 $x125)))
 (let (($x151 (= b0 (_ bv5 4))))
 (let (($x72 (= a0 (_ bv2 4))))
 (let (($x690 (and $x72 $x151)))
 (let (($x689 (and $x72 $x125)))
 (let (($x99 (= b0 (_ bv3 4))))
 (let (($x688 (and $x72 $x99)))
 (let (($x177 (= b0 (_ bv6 4))))
 (let (($x46 (= a0 (_ bv1 4))))
 (let (($x687 (and $x46 $x177)))
 (let (($x686 (and $x46 $x151)))
 (let (($x685 (and $x46 $x125)))
 (let (($x684 (and $x46 $x99)))
 (let (($x73 (= b0 (_ bv2 4))))
 (let (($x683 (and $x46 $x73)))
 (let (($x221 (= a0 (_ bv0 4))))
 (let (($x682 (and $x221 (= b0 (_ bv7 4)))))
 (let (($x680 (and $x221 $x177)))
 (let (($x679 (and $x221 $x151)))
 (let (($x678 (and $x221 $x125)))
 (let (($x677 (and $x221 $x99)))
 (let (($x676 (and $x221 $x73)))
 (let (($x47 (= b0 (_ bv1 4))))
 (let (($x675 (and $x221 $x47)))
 (or $x675 $x676 $x677 $x678 $x679 $x680 $x682 $x683 $x684 $x685 $x686 $x687 $x688 $x689 $x690 $x691))))))))))))))))))))))))))))
(assert
 (= w5 (_ bv274624 29)))
(check-sat)
