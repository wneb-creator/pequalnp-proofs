; benchmark generated from python API
(set-info :status unknown)
(declare-fun active0 () Bool)
(declare-fun active4 () Bool)
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
(declare-fun w0 () (_ BitVec 27))
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
 active4)
(assert
 (or (and active0 (or (= a0 (_ bv2 4)) (= b0 (_ bv2 4)))) (and active1 (or (= a1 (_ bv2 4)) (= b1 (_ bv2 4)))) (and active2 (or (= a2 (_ bv2 4)) (= b2 (_ bv2 4)))) (and active3 (or (= a3 (_ bv2 4)) (= b3 (_ bv2 4)))) (and active4 (or (= a4 (_ bv2 4)) (= b4 (_ bv2 4))))))
(assert
 (or (and active0 (or (= a0 (_ bv3 4)) (= b0 (_ bv3 4)))) (and active1 (or (= a1 (_ bv3 4)) (= b1 (_ bv3 4)))) (and active2 (or (= a2 (_ bv3 4)) (= b2 (_ bv3 4)))) (and active3 (or (= a3 (_ bv3 4)) (= b3 (_ bv3 4)))) (and active4 (or (= a4 (_ bv3 4)) (= b4 (_ bv3 4))))))
(assert
 (or (and active0 (or (= a0 (_ bv4 4)) (= b0 (_ bv4 4)))) (and active1 (or (= a1 (_ bv4 4)) (= b1 (_ bv4 4)))) (and active2 (or (= a2 (_ bv4 4)) (= b2 (_ bv4 4)))) (and active3 (or (= a3 (_ bv4 4)) (= b3 (_ bv4 4)))) (and active4 (or (= a4 (_ bv4 4)) (= b4 (_ bv4 4))))))
(assert
 (or (and active0 (or (= a0 (_ bv5 4)) (= b0 (_ bv5 4)))) (and active1 (or (= a1 (_ bv5 4)) (= b1 (_ bv5 4)))) (and active2 (or (= a2 (_ bv5 4)) (= b2 (_ bv5 4)))) (and active3 (or (= a3 (_ bv5 4)) (= b3 (_ bv5 4)))) (and active4 (or (= a4 (_ bv5 4)) (= b4 (_ bv5 4))))))
(assert
 (or (and active0 (or (= a0 (_ bv6 4)) (= b0 (_ bv6 4)))) (and active1 (or (= a1 (_ bv6 4)) (= b1 (_ bv6 4)))) (and active2 (or (= a2 (_ bv6 4)) (= b2 (_ bv6 4)))) (and active3 (or (= a3 (_ bv6 4)) (= b3 (_ bv6 4)))) (and active4 (or (= a4 (_ bv6 4)) (= b4 (_ bv6 4))))))
(assert
 (or (and active0 (or (= a0 (_ bv7 4)) (= b0 (_ bv7 4)))) (and active1 (or (= a1 (_ bv7 4)) (= b1 (_ bv7 4)))) (and active2 (or (= a2 (_ bv7 4)) (= b2 (_ bv7 4)))) (and active3 (or (= a3 (_ bv7 4)) (= b3 (_ bv7 4)))) (and active4 (or (= a4 (_ bv7 4)) (= b4 (_ bv7 4))))))
(assert
 (bvult b0 (_ bv8 4)))
(assert
 (=> active0 (bvult a0 b0)))
(assert
 (=> active0 (and (and (distinct a0 (_ bv0 4)) true) (and (distinct b0 (_ bv0 4)) true))))
(assert
 (=> active0 (and (and (distinct a0 (_ bv1 4)) true) (and (distinct b0 (_ bv1 4)) true))))
(assert
 (let (($x86 (= b0 (_ bv4 4))))
 (let ((?x197 (ite $x86 (_ bv67109856 27) (ite (= b0 (_ bv5 4)) (_ bv100695040 27) (ite (= b0 (_ bv6 4)) (_ bv101679104 27) (_ bv133169152 27))))))
 (let (($x64 (= b0 (_ bv3 4))))
 (let (($x42 (= b0 (_ bv2 4))))
 (let (($x200 (= b0 (_ bv1 4))))
 (let ((?x203 (ite (= b0 (_ bv0 4)) (_ bv102828113 27) (ite $x200 (_ bv104992914 27) (ite $x42 (_ bv42213652 27) (ite $x64 (_ bv17318424 27) ?x197))))))
 (let (($x85 (= a0 (_ bv4 4))))
 (let ((?x188 (ite $x85 (_ bv67109856 27) (ite (= a0 (_ bv5 4)) (_ bv100695040 27) (ite (= a0 (_ bv6 4)) (_ bv101679104 27) (_ bv133169152 27))))))
 (let (($x63 (= a0 (_ bv3 4))))
 (let (($x41 (= a0 (_ bv2 4))))
 (let (($x193 (= a0 (_ bv0 4))))
 (let ((?x194 (ite $x193 (_ bv102828113 27) (ite (= a0 (_ bv1 4)) (_ bv104992914 27) (ite $x41 (_ bv42213652 27) (ite $x63 (_ bv17318424 27) ?x188))))))
 (= w0 (ite and0 (bvand ?x194 ?x203) (bvor ?x194 ?x203))))))))))))))))
(assert
 (let (($x216 (and (and (distinct (_ bv102828113 27) w0) true) (and (distinct (_ bv104992914 27) w0) true) (and (distinct (_ bv42213652 27) w0) true) (and (distinct (_ bv17318424 27) w0) true) (and (distinct (_ bv67109856 27) w0) true) (and (distinct (_ bv100695040 27) w0) true) (and (distinct (_ bv101679104 27) w0) true) (and (distinct (_ bv133169152 27) w0) true))))
 (=> active0 $x216)))
(assert
 (let (($x234 (or (and active1 (or (= a1 (_ bv8 4)) (= b1 (_ bv8 4)))) (and active2 (or (= a2 (_ bv8 4)) (= b2 (_ bv8 4)))) (and active3 (or (= a3 (_ bv8 4)) (= b3 (_ bv8 4)))) (and active4 (or (= a4 (_ bv8 4)) (= b4 (_ bv8 4)))))))
 (let (($x235 (not active1)))
 (=> active0 (or $x235 $x234)))))
(assert
 (bvult b1 (_ bv9 4)))
(assert
 (=> active1 (bvult a1 b1)))
(assert
 (=> active1 (and (and (distinct a1 (_ bv0 4)) true) (and (distinct b1 (_ bv0 4)) true))))
(assert
 (=> active1 (and (and (distinct a1 (_ bv1 4)) true) (and (distinct b1 (_ bv1 4)) true))))
(assert
 (=> active1 active0))
(assert
 (let (($x235 (not active1)))
 (=> $x235 (and (= a1 (_ bv8 4)) (= b1 (_ bv8 4)) (not and1)))))
(assert
 (let (($x112 (= b1 (_ bv5 4))))
 (let ((?x266 (ite $x112 (_ bv100695040 27) (ite (= b1 (_ bv6 4)) (_ bv101679104 27) (ite (= b1 (_ bv7 4)) (_ bv133169152 27) w0)))))
 (let (($x90 (= b1 (_ bv4 4))))
 (let (($x68 (= b1 (_ bv3 4))))
 (let (($x46 (= b1 (_ bv2 4))))
 (let ((?x271 (ite (= b1 (_ bv1 4)) (_ bv104992914 27) (ite $x46 (_ bv42213652 27) (ite $x68 (_ bv17318424 27) (ite $x90 (_ bv67109856 27) ?x266))))))
 (let ((?x273 (ite (= b1 (_ bv0 4)) (_ bv102828113 27) ?x271)))
 (let (($x111 (= a1 (_ bv5 4))))
 (let ((?x256 (ite $x111 (_ bv100695040 27) (ite (= a1 (_ bv6 4)) (_ bv101679104 27) (ite (= a1 (_ bv7 4)) (_ bv133169152 27) w0)))))
 (let (($x89 (= a1 (_ bv4 4))))
 (let (($x67 (= a1 (_ bv3 4))))
 (let (($x45 (= a1 (_ bv2 4))))
 (let ((?x261 (ite (= a1 (_ bv1 4)) (_ bv104992914 27) (ite $x45 (_ bv42213652 27) (ite $x67 (_ bv17318424 27) (ite $x89 (_ bv67109856 27) ?x256))))))
 (let ((?x263 (ite (= a1 (_ bv0 4)) (_ bv102828113 27) ?x261)))
 (= w1 (ite and1 (bvand ?x263 ?x273) (bvor ?x263 ?x273))))))))))))))))))
(assert
 (let (($x287 (and (and (distinct (_ bv102828113 27) w1) true) (and (distinct (_ bv104992914 27) w1) true) (and (distinct (_ bv42213652 27) w1) true) (and (distinct (_ bv17318424 27) w1) true) (and (distinct (_ bv67109856 27) w1) true) (and (distinct (_ bv100695040 27) w1) true) (and (distinct (_ bv101679104 27) w1) true) (and (distinct (_ bv133169152 27) w1) true) (and (distinct w1 w0) true))))
 (=> active1 $x287)))
(assert
 (let (($x301 (or (and active2 (or (= a2 (_ bv9 4)) (= b2 (_ bv9 4)))) (and active3 (or (= a3 (_ bv9 4)) (= b3 (_ bv9 4)))) (and active4 (or (= a4 (_ bv9 4)) (= b4 (_ bv9 4)))))))
 (let (($x302 (not active2)))
 (=> active1 (or $x302 $x301)))))
(assert
 (bvult b2 (_ bv10 4)))
(assert
 (=> active2 (bvult a2 b2)))
(assert
 (=> active2 (and (and (distinct a2 (_ bv0 4)) true) (and (distinct b2 (_ bv0 4)) true))))
(assert
 (=> active2 (and (and (distinct a2 (_ bv1 4)) true) (and (distinct b2 (_ bv1 4)) true))))
(assert
 (=> active2 active1))
(assert
 (let (($x302 (not active2)))
 (=> $x302 (and (= a2 (_ bv9 4)) (= b2 (_ bv9 4)) (not and2)))))
(assert
 (let (($x138 (= b2 (_ bv6 4))))
 (let ((?x334 (ite $x138 (_ bv101679104 27) (ite (= b2 (_ bv7 4)) (_ bv133169152 27) (ite (= b2 (_ bv8 4)) w0 w1)))))
 (let (($x116 (= b2 (_ bv5 4))))
 (let (($x94 (= b2 (_ bv4 4))))
 (let (($x72 (= b2 (_ bv3 4))))
 (let (($x50 (= b2 (_ bv2 4))))
 (let ((?x340 (ite (= b2 (_ bv1 4)) (_ bv104992914 27) (ite $x50 (_ bv42213652 27) (ite $x72 (_ bv17318424 27) (ite $x94 (_ bv67109856 27) (ite $x116 (_ bv100695040 27) ?x334)))))))
 (let ((?x342 (ite (= b2 (_ bv0 4)) (_ bv102828113 27) ?x340)))
 (let (($x137 (= a2 (_ bv6 4))))
 (let ((?x323 (ite $x137 (_ bv101679104 27) (ite (= a2 (_ bv7 4)) (_ bv133169152 27) (ite (= a2 (_ bv8 4)) w0 w1)))))
 (let (($x115 (= a2 (_ bv5 4))))
 (let (($x93 (= a2 (_ bv4 4))))
 (let (($x71 (= a2 (_ bv3 4))))
 (let (($x49 (= a2 (_ bv2 4))))
 (let ((?x329 (ite (= a2 (_ bv1 4)) (_ bv104992914 27) (ite $x49 (_ bv42213652 27) (ite $x71 (_ bv17318424 27) (ite $x93 (_ bv67109856 27) (ite $x115 (_ bv100695040 27) ?x323)))))))
 (let ((?x331 (ite (= a2 (_ bv0 4)) (_ bv102828113 27) ?x329)))
 (= w2 (ite and2 (bvand ?x331 ?x342) (bvor ?x331 ?x342))))))))))))))))))))
(assert
 (let (($x357 (and (and (distinct (_ bv102828113 27) w2) true) (and (distinct (_ bv104992914 27) w2) true) (and (distinct (_ bv42213652 27) w2) true) (and (distinct (_ bv17318424 27) w2) true) (and (distinct (_ bv67109856 27) w2) true) (and (distinct (_ bv100695040 27) w2) true) (and (distinct (_ bv101679104 27) w2) true) (and (distinct (_ bv133169152 27) w2) true) (and (distinct w2 w0) true) (and (distinct w2 w1) true))))
 (=> active2 $x357)))
(assert
 (let (($x367 (or (and active3 (or (= a3 (_ bv10 4)) (= b3 (_ bv10 4)))) (and active4 (or (= a4 (_ bv10 4)) (= b4 (_ bv10 4)))))))
 (let (($x368 (not active3)))
 (=> active2 (or $x368 $x367)))))
(assert
 (bvult b3 (_ bv11 4)))
(assert
 (=> active3 (bvult a3 b3)))
(assert
 (=> active3 (and (and (distinct a3 (_ bv0 4)) true) (and (distinct b3 (_ bv0 4)) true))))
(assert
 (=> active3 (and (and (distinct a3 (_ bv1 4)) true) (and (distinct b3 (_ bv1 4)) true))))
(assert
 (=> active3 active2))
(assert
 (let (($x368 (not active3)))
 (=> $x368 (and (= a3 (_ bv10 4)) (= b3 (_ bv10 4)) (not and3)))))
(assert
 (let (($x164 (= b3 (_ bv7 4))))
 (let ((?x401 (ite $x164 (_ bv133169152 27) (ite (= b3 (_ bv8 4)) w0 (ite (= b3 (_ bv9 4)) w1 w2)))))
 (let (($x142 (= b3 (_ bv6 4))))
 (let (($x120 (= b3 (_ bv5 4))))
 (let (($x98 (= b3 (_ bv4 4))))
 (let (($x76 (= b3 (_ bv3 4))))
 (let (($x54 (= b3 (_ bv2 4))))
 (let ((?x406 (ite $x54 (_ bv42213652 27) (ite $x76 (_ bv17318424 27) (ite $x98 (_ bv67109856 27) (ite $x120 (_ bv100695040 27) (ite $x142 (_ bv101679104 27) ?x401)))))))
 (let ((?x410 (ite (= b3 (_ bv0 4)) (_ bv102828113 27) (ite (= b3 (_ bv1 4)) (_ bv104992914 27) ?x406))))
 (let (($x163 (= a3 (_ bv7 4))))
 (let ((?x389 (ite $x163 (_ bv133169152 27) (ite (= a3 (_ bv8 4)) w0 (ite (= a3 (_ bv9 4)) w1 w2)))))
 (let (($x141 (= a3 (_ bv6 4))))
 (let (($x119 (= a3 (_ bv5 4))))
 (let (($x97 (= a3 (_ bv4 4))))
 (let (($x75 (= a3 (_ bv3 4))))
 (let (($x53 (= a3 (_ bv2 4))))
 (let ((?x394 (ite $x53 (_ bv42213652 27) (ite $x75 (_ bv17318424 27) (ite $x97 (_ bv67109856 27) (ite $x119 (_ bv100695040 27) (ite $x141 (_ bv101679104 27) ?x389)))))))
 (let ((?x398 (ite (= a3 (_ bv0 4)) (_ bv102828113 27) (ite (= a3 (_ bv1 4)) (_ bv104992914 27) ?x394))))
 (= w3 (ite and3 (bvand ?x398 ?x410) (bvor ?x398 ?x410))))))))))))))))))))))
(assert
 (let (($x426 (and (and (distinct (_ bv102828113 27) w3) true) (and (distinct (_ bv104992914 27) w3) true) (and (distinct (_ bv42213652 27) w3) true) (and (distinct (_ bv17318424 27) w3) true) (and (distinct (_ bv67109856 27) w3) true) (and (distinct (_ bv100695040 27) w3) true) (and (distinct (_ bv101679104 27) w3) true) (and (distinct (_ bv133169152 27) w3) true) (and (distinct w3 w0) true) (and (distinct w3 w1) true) (and (distinct w3 w2) true))))
 (=> active3 $x426)))
(assert
 (let (($x432 (or (and active4 (or (= a4 (_ bv11 4)) (= b4 (_ bv11 4)))))))
 (let (($x433 (not active4)))
 (=> active3 (or $x433 $x432)))))
(assert
 (bvult b4 (_ bv12 4)))
(assert
 (=> active4 (bvult a4 b4)))
(assert
 (=> active4 (and (and (distinct a4 (_ bv0 4)) true) (and (distinct b4 (_ bv0 4)) true))))
(assert
 (=> active4 (and (and (distinct a4 (_ bv1 4)) true) (and (distinct b4 (_ bv1 4)) true))))
(assert
 (=> active4 active3))
(assert
 (let (($x433 (not active4)))
 (=> $x433 (and (= a4 (_ bv11 4)) (= b4 (_ bv11 4)) (not and4)))))
(assert
 (let (($x231 (= b4 (_ bv8 4))))
 (let ((?x467 (ite $x231 w0 (ite (= b4 (_ bv9 4)) w1 (ite (= b4 (_ bv10 4)) w2 w3)))))
 (let (($x168 (= b4 (_ bv7 4))))
 (let (($x146 (= b4 (_ bv6 4))))
 (let (($x124 (= b4 (_ bv5 4))))
 (let (($x102 (= b4 (_ bv4 4))))
 (let (($x80 (= b4 (_ bv3 4))))
 (let ((?x472 (ite $x80 (_ bv17318424 27) (ite $x102 (_ bv67109856 27) (ite $x124 (_ bv100695040 27) (ite $x146 (_ bv101679104 27) (ite $x168 (_ bv133169152 27) ?x467)))))))
 (let (($x58 (= b4 (_ bv2 4))))
 (let ((?x477 (ite (= b4 (_ bv0 4)) (_ bv102828113 27) (ite (= b4 (_ bv1 4)) (_ bv104992914 27) (ite $x58 (_ bv42213652 27) ?x472)))))
 (let (($x230 (= a4 (_ bv8 4))))
 (let ((?x454 (ite $x230 w0 (ite (= a4 (_ bv9 4)) w1 (ite (= a4 (_ bv10 4)) w2 w3)))))
 (let (($x167 (= a4 (_ bv7 4))))
 (let (($x145 (= a4 (_ bv6 4))))
 (let (($x123 (= a4 (_ bv5 4))))
 (let (($x101 (= a4 (_ bv4 4))))
 (let (($x79 (= a4 (_ bv3 4))))
 (let ((?x459 (ite $x79 (_ bv17318424 27) (ite $x101 (_ bv67109856 27) (ite $x123 (_ bv100695040 27) (ite $x145 (_ bv101679104 27) (ite $x167 (_ bv133169152 27) ?x454)))))))
 (let (($x57 (= a4 (_ bv2 4))))
 (let ((?x464 (ite (= a4 (_ bv0 4)) (_ bv102828113 27) (ite (= a4 (_ bv1 4)) (_ bv104992914 27) (ite $x57 (_ bv42213652 27) ?x459)))))
 (= w4 (ite and4 (bvand ?x464 ?x477) (bvor ?x464 ?x477))))))))))))))))))))))))
(assert
 (let (($x494 (and (and (distinct (_ bv102828113 27) w4) true) (and (distinct (_ bv104992914 27) w4) true) (and (distinct (_ bv42213652 27) w4) true) (and (distinct (_ bv17318424 27) w4) true) (and (distinct (_ bv67109856 27) w4) true) (and (distinct (_ bv100695040 27) w4) true) (and (distinct (_ bv101679104 27) w4) true) (and (distinct (_ bv133169152 27) w4) true) (and (distinct w4 w0) true) (and (distinct w4 w1) true) (and (distinct w4 w2) true) (and (distinct w4 w3) true))))
 (=> active4 $x494)))
(assert
 (let (($x506 (and (= a0 a1) (or (bvult b0 b1) (and (= b0 b1) (or and0 (not and1)))))))
 (=> (and active0 active1 (and (distinct a1 (_ bv8 4)) true) (and (distinct b1 (_ bv8 4)) true)) (or (bvult a0 a1) $x506))))
(assert
 (let (($x519 (and (= a1 a2) (or (bvult b1 b2) (and (= b1 b2) (or and1 (not and2)))))))
 (=> (and active1 active2 (and (distinct a2 (_ bv9 4)) true) (and (distinct b2 (_ bv9 4)) true)) (or (bvult a1 a2) $x519))))
(assert
 (let (($x532 (and (= a2 a3) (or (bvult b2 b3) (and (= b2 b3) (or and2 (not and3)))))))
 (=> (and active2 active3 (and (distinct a3 (_ bv10 4)) true) (and (distinct b3 (_ bv10 4)) true)) (or (bvult a2 a3) $x532))))
(assert
 (let (($x545 (and (= a3 a4) (or (bvult b3 b4) (and (= b3 b4) (or and3 (not and4)))))))
 (let (($x546 (or (bvult a3 a4) $x545)))
 (let (($x537 (and active3 active4 (and (distinct a4 (_ bv11 4)) true) (and (distinct b4 (_ bv11 4)) true))))
 (=> $x537 $x546)))))
(assert
 (let (($x130 (= b0 (_ bv6 4))))
 (let (($x107 (= a0 (_ bv5 4))))
 (let (($x559 (and $x107 $x130)))
 (let (($x108 (= b0 (_ bv5 4))))
 (let (($x85 (= a0 (_ bv4 4))))
 (let (($x558 (and $x85 $x108)))
 (let (($x63 (= a0 (_ bv3 4))))
 (let (($x557 (and $x63 $x108)))
 (let (($x86 (= b0 (_ bv4 4))))
 (let (($x556 (and $x63 $x86)))
 (let (($x41 (= a0 (_ bv2 4))))
 (let (($x555 (and $x41 $x108)))
 (let (($x554 (and $x41 $x86)))
 (let (($x64 (= b0 (_ bv3 4))))
 (let (($x553 (and $x41 $x64)))
 (let (($x193 (= a0 (_ bv0 4))))
 (let (($x552 (and $x193 $x108)))
 (let (($x551 (and $x193 $x86)))
 (let (($x550 (and $x193 $x64)))
 (let (($x42 (= b0 (_ bv2 4))))
 (let (($x549 (and $x193 $x42)))
 (let (($x200 (= b0 (_ bv1 4))))
 (let (($x548 (and $x193 $x200)))
 (or $x548 $x549 $x550 $x551 $x552 $x553 $x554 $x555 $x556 $x557 $x558 $x559)))))))))))))))))))))))))
(assert
 (= w4 (_ bv17318656 27)))
(check-sat)
