; benchmark generated from python API
(set-info :status unknown)
(declare-fun active0 () Bool)
(declare-fun active4 () Bool)
(declare-fun b6 () (_ BitVec 4))
(declare-fun a6 () (_ BitVec 4))
(declare-fun active6 () Bool)
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
(declare-fun and6 () Bool)
(declare-fun w6 () (_ BitVec 29))
(assert
 active0)
(assert
 active4)
(assert
 (or (and active0 (or (= a0 (_ bv1 4)) (= b0 (_ bv1 4)))) (and active1 (or (= a1 (_ bv1 4)) (= b1 (_ bv1 4)))) (and active2 (or (= a2 (_ bv1 4)) (= b2 (_ bv1 4)))) (and active3 (or (= a3 (_ bv1 4)) (= b3 (_ bv1 4)))) (and active4 (or (= a4 (_ bv1 4)) (= b4 (_ bv1 4)))) (and active5 (or (= a5 (_ bv1 4)) (= b5 (_ bv1 4)))) (and active6 (or (= a6 (_ bv1 4)) (= b6 (_ bv1 4))))))
(assert
 (or (and active0 (or (= a0 (_ bv2 4)) (= b0 (_ bv2 4)))) (and active1 (or (= a1 (_ bv2 4)) (= b1 (_ bv2 4)))) (and active2 (or (= a2 (_ bv2 4)) (= b2 (_ bv2 4)))) (and active3 (or (= a3 (_ bv2 4)) (= b3 (_ bv2 4)))) (and active4 (or (= a4 (_ bv2 4)) (= b4 (_ bv2 4)))) (and active5 (or (= a5 (_ bv2 4)) (= b5 (_ bv2 4)))) (and active6 (or (= a6 (_ bv2 4)) (= b6 (_ bv2 4))))))
(assert
 (or (and active0 (or (= a0 (_ bv3 4)) (= b0 (_ bv3 4)))) (and active1 (or (= a1 (_ bv3 4)) (= b1 (_ bv3 4)))) (and active2 (or (= a2 (_ bv3 4)) (= b2 (_ bv3 4)))) (and active3 (or (= a3 (_ bv3 4)) (= b3 (_ bv3 4)))) (and active4 (or (= a4 (_ bv3 4)) (= b4 (_ bv3 4)))) (and active5 (or (= a5 (_ bv3 4)) (= b5 (_ bv3 4)))) (and active6 (or (= a6 (_ bv3 4)) (= b6 (_ bv3 4))))))
(assert
 (or (and active0 (or (= a0 (_ bv4 4)) (= b0 (_ bv4 4)))) (and active1 (or (= a1 (_ bv4 4)) (= b1 (_ bv4 4)))) (and active2 (or (= a2 (_ bv4 4)) (= b2 (_ bv4 4)))) (and active3 (or (= a3 (_ bv4 4)) (= b3 (_ bv4 4)))) (and active4 (or (= a4 (_ bv4 4)) (= b4 (_ bv4 4)))) (and active5 (or (= a5 (_ bv4 4)) (= b5 (_ bv4 4)))) (and active6 (or (= a6 (_ bv4 4)) (= b6 (_ bv4 4))))))
(assert
 (or (and active0 (or (= a0 (_ bv5 4)) (= b0 (_ bv5 4)))) (and active1 (or (= a1 (_ bv5 4)) (= b1 (_ bv5 4)))) (and active2 (or (= a2 (_ bv5 4)) (= b2 (_ bv5 4)))) (and active3 (or (= a3 (_ bv5 4)) (= b3 (_ bv5 4)))) (and active4 (or (= a4 (_ bv5 4)) (= b4 (_ bv5 4)))) (and active5 (or (= a5 (_ bv5 4)) (= b5 (_ bv5 4)))) (and active6 (or (= a6 (_ bv5 4)) (= b6 (_ bv5 4))))))
(assert
 (or (and active0 (or (= a0 (_ bv6 4)) (= b0 (_ bv6 4)))) (and active1 (or (= a1 (_ bv6 4)) (= b1 (_ bv6 4)))) (and active2 (or (= a2 (_ bv6 4)) (= b2 (_ bv6 4)))) (and active3 (or (= a3 (_ bv6 4)) (= b3 (_ bv6 4)))) (and active4 (or (= a4 (_ bv6 4)) (= b4 (_ bv6 4)))) (and active5 (or (= a5 (_ bv6 4)) (= b5 (_ bv6 4)))) (and active6 (or (= a6 (_ bv6 4)) (= b6 (_ bv6 4))))))
(assert
 (bvult b0 (_ bv8 4)))
(assert
 (=> active0 (bvult a0 b0)))
(assert
 (=> active0 (and (and (distinct a0 (_ bv0 4)) true) (and (distinct b0 (_ bv0 4)) true))))
(assert
 (=> active0 (and (and (distinct a0 (_ bv7 4)) true) (and (distinct b0 (_ bv7 4)) true))))
(assert
 (let (($x142 (= b0 (_ bv4 4))))
 (let ((?x254 (ite $x142 (_ bv301990384 29) (ite (= b0 (_ bv5 4)) (_ bv335560192 29) (ite (= b0 (_ bv6 4)) (_ bv403161088 29) (_ bv536346624 29))))))
 (let (($x112 (= b0 (_ bv3 4))))
 (let (($x82 (= b0 (_ bv2 4))))
 (let (($x52 (= b0 (_ bv1 4))))
 (let ((?x259 (ite (= b0 (_ bv0 4)) (_ bv521176097 29) (ite $x52 (_ bv153159746 29) (ite $x82 (_ bv88215684 29) (ite $x112 (_ bv58990856 29) ?x254))))))
 (let (($x141 (= a0 (_ bv4 4))))
 (let ((?x246 (ite $x141 (_ bv301990384 29) (ite (= a0 (_ bv5 4)) (_ bv335560192 29) (ite (= a0 (_ bv6 4)) (_ bv403161088 29) (_ bv536346624 29))))))
 (let (($x111 (= a0 (_ bv3 4))))
 (let (($x81 (= a0 (_ bv2 4))))
 (let (($x51 (= a0 (_ bv1 4))))
 (let (($x250 (= a0 (_ bv0 4))))
 (let ((?x251 (ite $x250 (_ bv521176097 29) (ite $x51 (_ bv153159746 29) (ite $x81 (_ bv88215684 29) (ite $x111 (_ bv58990856 29) ?x246))))))
 (= w0 (ite and0 (bvand ?x251 ?x259) (bvor ?x251 ?x259)))))))))))))))))
(assert
 (let (($x272 (and (and (distinct (_ bv521176097 29) w0) true) (and (distinct (_ bv153159746 29) w0) true) (and (distinct (_ bv88215684 29) w0) true) (and (distinct (_ bv58990856 29) w0) true) (and (distinct (_ bv301990384 29) w0) true) (and (distinct (_ bv335560192 29) w0) true) (and (distinct (_ bv403161088 29) w0) true) (and (distinct (_ bv536346624 29) w0) true))))
 (=> active0 $x272)))
(assert
 (let (($x298 (or (and active1 (or (= a1 (_ bv8 4)) (= b1 (_ bv8 4)))) (and active2 (or (= a2 (_ bv8 4)) (= b2 (_ bv8 4)))) (and active3 (or (= a3 (_ bv8 4)) (= b3 (_ bv8 4)))) (and active4 (or (= a4 (_ bv8 4)) (= b4 (_ bv8 4)))) (and active5 (or (= a5 (_ bv8 4)) (= b5 (_ bv8 4)))) (and active6 (or (= a6 (_ bv8 4)) (= b6 (_ bv8 4)))))))
 (let (($x299 (not active1)))
 (=> active0 (or $x299 $x298)))))
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
 (let (($x299 (not active1)))
 (=> $x299 (and (= a1 (_ bv8 4)) (= b1 (_ bv8 4)) (not and1)))))
(assert
 (let (($x176 (= b1 (_ bv5 4))))
 (let ((?x331 (ite $x176 (_ bv335560192 29) (ite (= b1 (_ bv6 4)) (_ bv403161088 29) (ite (= b1 (_ bv7 4)) (_ bv536346624 29) w0)))))
 (let (($x146 (= b1 (_ bv4 4))))
 (let (($x116 (= b1 (_ bv3 4))))
 (let (($x86 (= b1 (_ bv2 4))))
 (let (($x56 (= b1 (_ bv1 4))))
 (let ((?x337 (ite (= b1 (_ bv0 4)) (_ bv521176097 29) (ite $x56 (_ bv153159746 29) (ite $x86 (_ bv88215684 29) (ite $x116 (_ bv58990856 29) (ite $x146 (_ bv301990384 29) ?x331)))))))
 (let (($x175 (= a1 (_ bv5 4))))
 (let ((?x321 (ite $x175 (_ bv335560192 29) (ite (= a1 (_ bv6 4)) (_ bv403161088 29) (ite (= a1 (_ bv7 4)) (_ bv536346624 29) w0)))))
 (let (($x145 (= a1 (_ bv4 4))))
 (let (($x115 (= a1 (_ bv3 4))))
 (let (($x85 (= a1 (_ bv2 4))))
 (let (($x55 (= a1 (_ bv1 4))))
 (let ((?x327 (ite (= a1 (_ bv0 4)) (_ bv521176097 29) (ite $x55 (_ bv153159746 29) (ite $x85 (_ bv88215684 29) (ite $x115 (_ bv58990856 29) (ite $x145 (_ bv301990384 29) ?x321)))))))
 (= w1 (ite and1 (bvand ?x327 ?x337) (bvor ?x327 ?x337))))))))))))))))))
(assert
 (let (($x351 (and (and (distinct (_ bv521176097 29) w1) true) (and (distinct (_ bv153159746 29) w1) true) (and (distinct (_ bv88215684 29) w1) true) (and (distinct (_ bv58990856 29) w1) true) (and (distinct (_ bv301990384 29) w1) true) (and (distinct (_ bv335560192 29) w1) true) (and (distinct (_ bv403161088 29) w1) true) (and (distinct (_ bv536346624 29) w1) true) (and (distinct w1 w0) true))))
 (=> active1 $x351)))
(assert
 (let (($x373 (or (and active2 (or (= a2 (_ bv9 4)) (= b2 (_ bv9 4)))) (and active3 (or (= a3 (_ bv9 4)) (= b3 (_ bv9 4)))) (and active4 (or (= a4 (_ bv9 4)) (= b4 (_ bv9 4)))) (and active5 (or (= a5 (_ bv9 4)) (= b5 (_ bv9 4)))) (and active6 (or (= a6 (_ bv9 4)) (= b6 (_ bv9 4)))))))
 (let (($x374 (not active2)))
 (=> active1 (or $x374 $x373)))))
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
 (let (($x374 (not active2)))
 (=> $x374 (and (= a2 (_ bv9 4)) (= b2 (_ bv9 4)) (not and2)))))
(assert
 (let (($x210 (= b2 (_ bv6 4))))
 (let ((?x407 (ite $x210 (_ bv403161088 29) (ite (= b2 (_ bv7 4)) (_ bv536346624 29) (ite (= b2 (_ bv8 4)) w0 w1)))))
 (let (($x180 (= b2 (_ bv5 4))))
 (let (($x150 (= b2 (_ bv4 4))))
 (let (($x120 (= b2 (_ bv3 4))))
 (let (($x90 (= b2 (_ bv2 4))))
 (let (($x60 (= b2 (_ bv1 4))))
 (let ((?x412 (ite $x60 (_ bv153159746 29) (ite $x90 (_ bv88215684 29) (ite $x120 (_ bv58990856 29) (ite $x150 (_ bv301990384 29) (ite $x180 (_ bv335560192 29) ?x407)))))))
 (let ((?x414 (ite (= b2 (_ bv0 4)) (_ bv521176097 29) ?x412)))
 (let (($x209 (= a2 (_ bv6 4))))
 (let ((?x396 (ite $x209 (_ bv403161088 29) (ite (= a2 (_ bv7 4)) (_ bv536346624 29) (ite (= a2 (_ bv8 4)) w0 w1)))))
 (let (($x179 (= a2 (_ bv5 4))))
 (let (($x149 (= a2 (_ bv4 4))))
 (let (($x119 (= a2 (_ bv3 4))))
 (let (($x89 (= a2 (_ bv2 4))))
 (let (($x59 (= a2 (_ bv1 4))))
 (let ((?x401 (ite $x59 (_ bv153159746 29) (ite $x89 (_ bv88215684 29) (ite $x119 (_ bv58990856 29) (ite $x149 (_ bv301990384 29) (ite $x179 (_ bv335560192 29) ?x396)))))))
 (let ((?x403 (ite (= a2 (_ bv0 4)) (_ bv521176097 29) ?x401)))
 (= w2 (ite and2 (bvand ?x403 ?x414) (bvor ?x403 ?x414))))))))))))))))))))))
(assert
 (let (($x429 (and (and (distinct (_ bv521176097 29) w2) true) (and (distinct (_ bv153159746 29) w2) true) (and (distinct (_ bv88215684 29) w2) true) (and (distinct (_ bv58990856 29) w2) true) (and (distinct (_ bv301990384 29) w2) true) (and (distinct (_ bv335560192 29) w2) true) (and (distinct (_ bv403161088 29) w2) true) (and (distinct (_ bv536346624 29) w2) true) (and (distinct w2 w0) true) (and (distinct w2 w1) true))))
 (=> active2 $x429)))
(assert
 (let (($x447 (or (and active3 (or (= a3 (_ bv10 4)) (= b3 (_ bv10 4)))) (and active4 (or (= a4 (_ bv10 4)) (= b4 (_ bv10 4)))) (and active5 (or (= a5 (_ bv10 4)) (= b5 (_ bv10 4)))) (and active6 (or (= a6 (_ bv10 4)) (= b6 (_ bv10 4)))))))
 (let (($x448 (not active3)))
 (=> active2 (or $x448 $x447)))))
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
 (let (($x448 (not active3)))
 (=> $x448 (and (= a3 (_ bv10 4)) (= b3 (_ bv10 4)) (not and3)))))
(assert
 (let ((?x482 (ite (= b3 (_ bv7 4)) (_ bv536346624 29) (ite (= b3 (_ bv8 4)) w0 (ite (= b3 (_ bv9 4)) w1 w2)))))
 (let (($x214 (= b3 (_ bv6 4))))
 (let (($x184 (= b3 (_ bv5 4))))
 (let (($x154 (= b3 (_ bv4 4))))
 (let (($x124 (= b3 (_ bv3 4))))
 (let (($x94 (= b3 (_ bv2 4))))
 (let ((?x487 (ite $x94 (_ bv88215684 29) (ite $x124 (_ bv58990856 29) (ite $x154 (_ bv301990384 29) (ite $x184 (_ bv335560192 29) (ite $x214 (_ bv403161088 29) ?x482)))))))
 (let (($x64 (= b3 (_ bv1 4))))
 (let ((?x490 (ite (= b3 (_ bv0 4)) (_ bv521176097 29) (ite $x64 (_ bv153159746 29) ?x487))))
 (let ((?x470 (ite (= a3 (_ bv7 4)) (_ bv536346624 29) (ite (= a3 (_ bv8 4)) w0 (ite (= a3 (_ bv9 4)) w1 w2)))))
 (let (($x213 (= a3 (_ bv6 4))))
 (let (($x183 (= a3 (_ bv5 4))))
 (let (($x153 (= a3 (_ bv4 4))))
 (let (($x123 (= a3 (_ bv3 4))))
 (let (($x93 (= a3 (_ bv2 4))))
 (let ((?x475 (ite $x93 (_ bv88215684 29) (ite $x123 (_ bv58990856 29) (ite $x153 (_ bv301990384 29) (ite $x183 (_ bv335560192 29) (ite $x213 (_ bv403161088 29) ?x470)))))))
 (let (($x63 (= a3 (_ bv1 4))))
 (let ((?x478 (ite (= a3 (_ bv0 4)) (_ bv521176097 29) (ite $x63 (_ bv153159746 29) ?x475))))
 (= w3 (ite and3 (bvand ?x478 ?x490) (bvor ?x478 ?x490))))))))))))))))))))))
(assert
 (let (($x506 (and (and (distinct (_ bv521176097 29) w3) true) (and (distinct (_ bv153159746 29) w3) true) (and (distinct (_ bv88215684 29) w3) true) (and (distinct (_ bv58990856 29) w3) true) (and (distinct (_ bv301990384 29) w3) true) (and (distinct (_ bv335560192 29) w3) true) (and (distinct (_ bv403161088 29) w3) true) (and (distinct (_ bv536346624 29) w3) true) (and (distinct w3 w0) true) (and (distinct w3 w1) true) (and (distinct w3 w2) true))))
 (=> active3 $x506)))
(assert
 (let (($x520 (or (and active4 (or (= a4 (_ bv11 4)) (= b4 (_ bv11 4)))) (and active5 (or (= a5 (_ bv11 4)) (= b5 (_ bv11 4)))) (and active6 (or (= a6 (_ bv11 4)) (= b6 (_ bv11 4)))))))
 (let (($x521 (not active4)))
 (=> active3 (or $x521 $x520)))))
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
 (let (($x521 (not active4)))
 (=> $x521 (and (= a4 (_ bv11 4)) (= b4 (_ bv11 4)) (not and4)))))
(assert
 (let (($x287 (= b4 (_ bv8 4))))
 (let ((?x555 (ite $x287 w0 (ite (= b4 (_ bv9 4)) w1 (ite (= b4 (_ bv10 4)) w2 w3)))))
 (let (($x218 (= b4 (_ bv6 4))))
 (let (($x188 (= b4 (_ bv5 4))))
 (let (($x158 (= b4 (_ bv4 4))))
 (let ((?x560 (ite $x158 (_ bv301990384 29) (ite $x188 (_ bv335560192 29) (ite $x218 (_ bv403161088 29) (ite (= b4 (_ bv7 4)) (_ bv536346624 29) ?x555))))))
 (let (($x128 (= b4 (_ bv3 4))))
 (let (($x98 (= b4 (_ bv2 4))))
 (let (($x68 (= b4 (_ bv1 4))))
 (let ((?x565 (ite (= b4 (_ bv0 4)) (_ bv521176097 29) (ite $x68 (_ bv153159746 29) (ite $x98 (_ bv88215684 29) (ite $x128 (_ bv58990856 29) ?x560))))))
 (let (($x286 (= a4 (_ bv8 4))))
 (let ((?x542 (ite $x286 w0 (ite (= a4 (_ bv9 4)) w1 (ite (= a4 (_ bv10 4)) w2 w3)))))
 (let (($x217 (= a4 (_ bv6 4))))
 (let (($x187 (= a4 (_ bv5 4))))
 (let (($x157 (= a4 (_ bv4 4))))
 (let ((?x547 (ite $x157 (_ bv301990384 29) (ite $x187 (_ bv335560192 29) (ite $x217 (_ bv403161088 29) (ite (= a4 (_ bv7 4)) (_ bv536346624 29) ?x542))))))
 (let (($x127 (= a4 (_ bv3 4))))
 (let (($x97 (= a4 (_ bv2 4))))
 (let (($x67 (= a4 (_ bv1 4))))
 (let ((?x552 (ite (= a4 (_ bv0 4)) (_ bv521176097 29) (ite $x67 (_ bv153159746 29) (ite $x97 (_ bv88215684 29) (ite $x127 (_ bv58990856 29) ?x547))))))
 (= w4 (ite and4 (bvand ?x552 ?x565) (bvor ?x552 ?x565))))))))))))))))))))))))
(assert
 (let (($x582 (and (and (distinct (_ bv521176097 29) w4) true) (and (distinct (_ bv153159746 29) w4) true) (and (distinct (_ bv88215684 29) w4) true) (and (distinct (_ bv58990856 29) w4) true) (and (distinct (_ bv301990384 29) w4) true) (and (distinct (_ bv335560192 29) w4) true) (and (distinct (_ bv403161088 29) w4) true) (and (distinct (_ bv536346624 29) w4) true) (and (distinct w4 w0) true) (and (distinct w4 w1) true) (and (distinct w4 w2) true) (and (distinct w4 w3) true))))
 (=> active4 $x582)))
(assert
 (let (($x592 (or (and active5 (or (= a5 (_ bv12 4)) (= b5 (_ bv12 4)))) (and active6 (or (= a6 (_ bv12 4)) (= b6 (_ bv12 4)))))))
 (let (($x593 (not active5)))
 (=> active4 (or $x593 $x592)))))
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
 (let (($x593 (not active5)))
 (=> $x593 (and (= a5 (_ bv12 4)) (= b5 (_ bv12 4)) (not and5)))))
(assert
 (let (($x366 (= b5 (_ bv9 4))))
 (let ((?x628 (ite $x366 w1 (ite (= b5 (_ bv10 4)) w2 (ite (= b5 (_ bv11 4)) w3 w4)))))
 (let (($x291 (= b5 (_ bv8 4))))
 (let (($x222 (= b5 (_ bv6 4))))
 (let (($x192 (= b5 (_ bv5 4))))
 (let ((?x633 (ite $x192 (_ bv335560192 29) (ite $x222 (_ bv403161088 29) (ite (= b5 (_ bv7 4)) (_ bv536346624 29) (ite $x291 w0 ?x628))))))
 (let (($x162 (= b5 (_ bv4 4))))
 (let (($x132 (= b5 (_ bv3 4))))
 (let (($x102 (= b5 (_ bv2 4))))
 (let (($x72 (= b5 (_ bv1 4))))
 (let ((?x639 (ite (= b5 (_ bv0 4)) (_ bv521176097 29) (ite $x72 (_ bv153159746 29) (ite $x102 (_ bv88215684 29) (ite $x132 (_ bv58990856 29) (ite $x162 (_ bv301990384 29) ?x633)))))))
 (let (($x365 (= a5 (_ bv9 4))))
 (let ((?x614 (ite $x365 w1 (ite (= a5 (_ bv10 4)) w2 (ite (= a5 (_ bv11 4)) w3 w4)))))
 (let (($x290 (= a5 (_ bv8 4))))
 (let (($x221 (= a5 (_ bv6 4))))
 (let (($x191 (= a5 (_ bv5 4))))
 (let ((?x619 (ite $x191 (_ bv335560192 29) (ite $x221 (_ bv403161088 29) (ite (= a5 (_ bv7 4)) (_ bv536346624 29) (ite $x290 w0 ?x614))))))
 (let (($x161 (= a5 (_ bv4 4))))
 (let (($x131 (= a5 (_ bv3 4))))
 (let (($x101 (= a5 (_ bv2 4))))
 (let (($x71 (= a5 (_ bv1 4))))
 (let ((?x625 (ite (= a5 (_ bv0 4)) (_ bv521176097 29) (ite $x71 (_ bv153159746 29) (ite $x101 (_ bv88215684 29) (ite $x131 (_ bv58990856 29) (ite $x161 (_ bv301990384 29) ?x619)))))))
 (= w5 (ite and5 (bvand ?x625 ?x639) (bvor ?x625 ?x639))))))))))))))))))))))))))
(assert
 (let (($x657 (and (and (distinct (_ bv521176097 29) w5) true) (and (distinct (_ bv153159746 29) w5) true) (and (distinct (_ bv88215684 29) w5) true) (and (distinct (_ bv58990856 29) w5) true) (and (distinct (_ bv301990384 29) w5) true) (and (distinct (_ bv335560192 29) w5) true) (and (distinct (_ bv403161088 29) w5) true) (and (distinct (_ bv536346624 29) w5) true) (and (distinct w5 w0) true) (and (distinct w5 w1) true) (and (distinct w5 w2) true) (and (distinct w5 w3) true) (and (distinct w5 w4) true))))
 (=> active5 $x657)))
(assert
 (let (($x663 (or (and active6 (or (= a6 (_ bv13 4)) (= b6 (_ bv13 4)))))))
 (let (($x664 (not active6)))
 (=> active5 (or $x664 $x663)))))
(assert
 (bvult b6 (_ bv14 4)))
(assert
 (=> active6 (bvult a6 b6)))
(assert
 (=> active6 (and (and (distinct a6 (_ bv0 4)) true) (and (distinct b6 (_ bv0 4)) true))))
(assert
 (=> active6 (and (and (distinct a6 (_ bv7 4)) true) (and (distinct b6 (_ bv7 4)) true))))
(assert
 (=> active6 active5))
(assert
 (let (($x664 (not active6)))
 (=> $x664 (and (= a6 (_ bv13 4)) (= b6 (_ bv13 4)) (not and6)))))
(assert
 (let (($x444 (= b6 (_ bv10 4))))
 (let ((?x700 (ite $x444 w2 (ite (= b6 (_ bv11 4)) w3 (ite (= b6 (_ bv12 4)) w4 w5)))))
 (let (($x370 (= b6 (_ bv9 4))))
 (let (($x295 (= b6 (_ bv8 4))))
 (let (($x226 (= b6 (_ bv6 4))))
 (let ((?x705 (ite $x226 (_ bv403161088 29) (ite (= b6 (_ bv7 4)) (_ bv536346624 29) (ite $x295 w0 (ite $x370 w1 ?x700))))))
 (let (($x196 (= b6 (_ bv5 4))))
 (let (($x166 (= b6 (_ bv4 4))))
 (let (($x136 (= b6 (_ bv3 4))))
 (let (($x106 (= b6 (_ bv2 4))))
 (let (($x76 (= b6 (_ bv1 4))))
 (let ((?x710 (ite $x76 (_ bv153159746 29) (ite $x106 (_ bv88215684 29) (ite $x136 (_ bv58990856 29) (ite $x166 (_ bv301990384 29) (ite $x196 (_ bv335560192 29) ?x705)))))))
 (let ((?x712 (ite (= b6 (_ bv0 4)) (_ bv521176097 29) ?x710)))
 (let (($x443 (= a6 (_ bv10 4))))
 (let ((?x685 (ite $x443 w2 (ite (= a6 (_ bv11 4)) w3 (ite (= a6 (_ bv12 4)) w4 w5)))))
 (let (($x369 (= a6 (_ bv9 4))))
 (let (($x294 (= a6 (_ bv8 4))))
 (let (($x225 (= a6 (_ bv6 4))))
 (let ((?x690 (ite $x225 (_ bv403161088 29) (ite (= a6 (_ bv7 4)) (_ bv536346624 29) (ite $x294 w0 (ite $x369 w1 ?x685))))))
 (let (($x195 (= a6 (_ bv5 4))))
 (let (($x165 (= a6 (_ bv4 4))))
 (let (($x135 (= a6 (_ bv3 4))))
 (let (($x105 (= a6 (_ bv2 4))))
 (let (($x75 (= a6 (_ bv1 4))))
 (let ((?x695 (ite $x75 (_ bv153159746 29) (ite $x105 (_ bv88215684 29) (ite $x135 (_ bv58990856 29) (ite $x165 (_ bv301990384 29) (ite $x195 (_ bv335560192 29) ?x690)))))))
 (let ((?x697 (ite (= a6 (_ bv0 4)) (_ bv521176097 29) ?x695)))
 (= w6 (ite and6 (bvand ?x697 ?x712) (bvor ?x697 ?x712))))))))))))))))))))))))))))))
(assert
 (let (($x731 (and (and (distinct (_ bv521176097 29) w6) true) (and (distinct (_ bv153159746 29) w6) true) (and (distinct (_ bv88215684 29) w6) true) (and (distinct (_ bv58990856 29) w6) true) (and (distinct (_ bv301990384 29) w6) true) (and (distinct (_ bv335560192 29) w6) true) (and (distinct (_ bv403161088 29) w6) true) (and (distinct (_ bv536346624 29) w6) true) (and (distinct w6 w0) true) (and (distinct w6 w1) true) (and (distinct w6 w2) true) (and (distinct w6 w3) true) (and (distinct w6 w4) true) (and (distinct w6 w5) true))))
 (=> active6 $x731)))
(assert
 (let (($x743 (and (= a0 a1) (or (bvult b0 b1) (and (= b0 b1) (or and0 (not and1)))))))
 (=> (and active0 active1 (and (distinct a1 (_ bv8 4)) true) (and (distinct b1 (_ bv8 4)) true)) (or (bvult a0 a1) $x743))))
(assert
 (let (($x756 (and (= a1 a2) (or (bvult b1 b2) (and (= b1 b2) (or and1 (not and2)))))))
 (=> (and active1 active2 (and (distinct a2 (_ bv9 4)) true) (and (distinct b2 (_ bv9 4)) true)) (or (bvult a1 a2) $x756))))
(assert
 (let (($x769 (and (= a2 a3) (or (bvult b2 b3) (and (= b2 b3) (or and2 (not and3)))))))
 (=> (and active2 active3 (and (distinct a3 (_ bv10 4)) true) (and (distinct b3 (_ bv10 4)) true)) (or (bvult a2 a3) $x769))))
(assert
 (let (($x782 (and (= a3 a4) (or (bvult b3 b4) (and (= b3 b4) (or and3 (not and4)))))))
 (=> (and active3 active4 (and (distinct a4 (_ bv11 4)) true) (and (distinct b4 (_ bv11 4)) true)) (or (bvult a3 a4) $x782))))
(assert
 (let (($x795 (and (= a4 a5) (or (bvult b4 b5) (and (= b4 b5) (or and4 (not and5)))))))
 (=> (and active4 active5 (and (distinct a5 (_ bv12 4)) true) (and (distinct b5 (_ bv12 4)) true)) (or (bvult a4 a5) $x795))))
(assert
 (let (($x808 (and (= a5 a6) (or (bvult b5 b6) (and (= b5 b6) (or and5 (not and6)))))))
 (let (($x809 (or (bvult a5 a6) $x808)))
 (let (($x800 (and active5 active6 (and (distinct a6 (_ bv13 4)) true) (and (distinct b6 (_ bv13 4)) true))))
 (=> $x800 $x809)))))
(assert
 (let (($x202 (= b0 (_ bv6 4))))
 (let (($x51 (= a0 (_ bv1 4))))
 (let (($x817 (and $x51 $x202)))
 (let (($x142 (= b0 (_ bv4 4))))
 (let (($x816 (and $x51 $x142)))
 (let (($x82 (= b0 (_ bv2 4))))
 (let (($x815 (and $x51 $x82)))
 (let (($x250 (= a0 (_ bv0 4))))
 (let (($x814 (and $x250 (= b0 (_ bv7 4)))))
 (let (($x812 (and $x250 $x142)))
 (let (($x52 (= b0 (_ bv1 4))))
 (let (($x811 (and $x250 $x52)))
 (or $x811 $x812 $x814 $x815 $x816 $x817))))))))))))))
(assert
 (= w6 (_ bv403648 29)))
(check-sat)
