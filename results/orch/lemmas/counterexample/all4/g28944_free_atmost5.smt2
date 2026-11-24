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
 (or (and active0 (or (= a0 (_ bv1 4)) (= b0 (_ bv1 4)))) (and active1 (or (= a1 (_ bv1 4)) (= b1 (_ bv1 4)))) (and active2 (or (= a2 (_ bv1 4)) (= b2 (_ bv1 4)))) (and active3 (or (= a3 (_ bv1 4)) (= b3 (_ bv1 4)))) (and active4 (or (= a4 (_ bv1 4)) (= b4 (_ bv1 4))))))
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
 (bvult b0 (_ bv8 4)))
(assert
 (=> active0 (bvult a0 b0)))
(assert
 (=> active0 (and (and (distinct a0 (_ bv0 4)) true) (and (distinct b0 (_ bv0 4)) true))))
(assert
 (=> active0 (and (and (distinct a0 (_ bv7 4)) true) (and (distinct b0 (_ bv7 4)) true))))
(assert
 (let (($x108 (= b0 (_ bv4 4))))
 (let ((?x196 (ite $x108 (_ bv67109360 27) (ite (= b0 (_ bv5 4)) (_ bv100679168 27) (ite (= b0 (_ bv6 4)) (_ bv101171200 27) (_ bv133693440 27))))))
 (let (($x86 (= b0 (_ bv3 4))))
 (let (($x64 (= b0 (_ bv2 4))))
 (let (($x42 (= b0 (_ bv1 4))))
 (let ((?x201 (ite (= b0 (_ bv0 4)) (_ bv118522913 27) (ite $x42 (_ bv52496450 27) (ite $x64 (_ bv54661252 27) (ite $x86 (_ bv25436424 27) ?x196))))))
 (let (($x107 (= a0 (_ bv4 4))))
 (let ((?x188 (ite $x107 (_ bv67109360 27) (ite (= a0 (_ bv5 4)) (_ bv100679168 27) (ite (= a0 (_ bv6 4)) (_ bv101171200 27) (_ bv133693440 27))))))
 (let (($x85 (= a0 (_ bv3 4))))
 (let (($x63 (= a0 (_ bv2 4))))
 (let (($x41 (= a0 (_ bv1 4))))
 (let (($x192 (= a0 (_ bv0 4))))
 (let ((?x193 (ite $x192 (_ bv118522913 27) (ite $x41 (_ bv52496450 27) (ite $x63 (_ bv54661252 27) (ite $x85 (_ bv25436424 27) ?x188))))))
 (= w0 (ite and0 (bvand ?x193 ?x201) (bvor ?x193 ?x201)))))))))))))))))
(assert
 (let (($x214 (and (and (distinct (_ bv118522913 27) w0) true) (and (distinct (_ bv52496450 27) w0) true) (and (distinct (_ bv54661252 27) w0) true) (and (distinct (_ bv25436424 27) w0) true) (and (distinct (_ bv67109360 27) w0) true) (and (distinct (_ bv100679168 27) w0) true) (and (distinct (_ bv101171200 27) w0) true) (and (distinct (_ bv133693440 27) w0) true))))
 (=> active0 $x214)))
(assert
 (let (($x232 (or (and active1 (or (= a1 (_ bv8 4)) (= b1 (_ bv8 4)))) (and active2 (or (= a2 (_ bv8 4)) (= b2 (_ bv8 4)))) (and active3 (or (= a3 (_ bv8 4)) (= b3 (_ bv8 4)))) (and active4 (or (= a4 (_ bv8 4)) (= b4 (_ bv8 4)))))))
 (let (($x233 (not active1)))
 (=> active0 (or $x233 $x232)))))
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
 (let (($x233 (not active1)))
 (=> $x233 (and (= a1 (_ bv8 4)) (= b1 (_ bv8 4)) (not and1)))))
(assert
 (let (($x134 (= b1 (_ bv5 4))))
 (let ((?x265 (ite $x134 (_ bv100679168 27) (ite (= b1 (_ bv6 4)) (_ bv101171200 27) (ite (= b1 (_ bv7 4)) (_ bv133693440 27) w0)))))
 (let (($x112 (= b1 (_ bv4 4))))
 (let (($x90 (= b1 (_ bv3 4))))
 (let (($x68 (= b1 (_ bv2 4))))
 (let (($x46 (= b1 (_ bv1 4))))
 (let ((?x271 (ite (= b1 (_ bv0 4)) (_ bv118522913 27) (ite $x46 (_ bv52496450 27) (ite $x68 (_ bv54661252 27) (ite $x90 (_ bv25436424 27) (ite $x112 (_ bv67109360 27) ?x265)))))))
 (let (($x133 (= a1 (_ bv5 4))))
 (let ((?x255 (ite $x133 (_ bv100679168 27) (ite (= a1 (_ bv6 4)) (_ bv101171200 27) (ite (= a1 (_ bv7 4)) (_ bv133693440 27) w0)))))
 (let (($x111 (= a1 (_ bv4 4))))
 (let (($x89 (= a1 (_ bv3 4))))
 (let (($x67 (= a1 (_ bv2 4))))
 (let (($x45 (= a1 (_ bv1 4))))
 (let ((?x261 (ite (= a1 (_ bv0 4)) (_ bv118522913 27) (ite $x45 (_ bv52496450 27) (ite $x67 (_ bv54661252 27) (ite $x89 (_ bv25436424 27) (ite $x111 (_ bv67109360 27) ?x255)))))))
 (= w1 (ite and1 (bvand ?x261 ?x271) (bvor ?x261 ?x271))))))))))))))))))
(assert
 (let (($x285 (and (and (distinct (_ bv118522913 27) w1) true) (and (distinct (_ bv52496450 27) w1) true) (and (distinct (_ bv54661252 27) w1) true) (and (distinct (_ bv25436424 27) w1) true) (and (distinct (_ bv67109360 27) w1) true) (and (distinct (_ bv100679168 27) w1) true) (and (distinct (_ bv101171200 27) w1) true) (and (distinct (_ bv133693440 27) w1) true) (and (distinct w1 w0) true))))
 (=> active1 $x285)))
(assert
 (let (($x299 (or (and active2 (or (= a2 (_ bv9 4)) (= b2 (_ bv9 4)))) (and active3 (or (= a3 (_ bv9 4)) (= b3 (_ bv9 4)))) (and active4 (or (= a4 (_ bv9 4)) (= b4 (_ bv9 4)))))))
 (let (($x300 (not active2)))
 (=> active1 (or $x300 $x299)))))
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
 (let (($x300 (not active2)))
 (=> $x300 (and (= a2 (_ bv9 4)) (= b2 (_ bv9 4)) (not and2)))))
(assert
 (let (($x160 (= b2 (_ bv6 4))))
 (let ((?x333 (ite $x160 (_ bv101171200 27) (ite (= b2 (_ bv7 4)) (_ bv133693440 27) (ite (= b2 (_ bv8 4)) w0 w1)))))
 (let (($x138 (= b2 (_ bv5 4))))
 (let (($x116 (= b2 (_ bv4 4))))
 (let (($x94 (= b2 (_ bv3 4))))
 (let (($x72 (= b2 (_ bv2 4))))
 (let (($x50 (= b2 (_ bv1 4))))
 (let ((?x338 (ite $x50 (_ bv52496450 27) (ite $x72 (_ bv54661252 27) (ite $x94 (_ bv25436424 27) (ite $x116 (_ bv67109360 27) (ite $x138 (_ bv100679168 27) ?x333)))))))
 (let ((?x340 (ite (= b2 (_ bv0 4)) (_ bv118522913 27) ?x338)))
 (let (($x159 (= a2 (_ bv6 4))))
 (let ((?x322 (ite $x159 (_ bv101171200 27) (ite (= a2 (_ bv7 4)) (_ bv133693440 27) (ite (= a2 (_ bv8 4)) w0 w1)))))
 (let (($x137 (= a2 (_ bv5 4))))
 (let (($x115 (= a2 (_ bv4 4))))
 (let (($x93 (= a2 (_ bv3 4))))
 (let (($x71 (= a2 (_ bv2 4))))
 (let (($x49 (= a2 (_ bv1 4))))
 (let ((?x327 (ite $x49 (_ bv52496450 27) (ite $x71 (_ bv54661252 27) (ite $x93 (_ bv25436424 27) (ite $x115 (_ bv67109360 27) (ite $x137 (_ bv100679168 27) ?x322)))))))
 (let ((?x329 (ite (= a2 (_ bv0 4)) (_ bv118522913 27) ?x327)))
 (= w2 (ite and2 (bvand ?x329 ?x340) (bvor ?x329 ?x340))))))))))))))))))))))
(assert
 (let (($x355 (and (and (distinct (_ bv118522913 27) w2) true) (and (distinct (_ bv52496450 27) w2) true) (and (distinct (_ bv54661252 27) w2) true) (and (distinct (_ bv25436424 27) w2) true) (and (distinct (_ bv67109360 27) w2) true) (and (distinct (_ bv100679168 27) w2) true) (and (distinct (_ bv101171200 27) w2) true) (and (distinct (_ bv133693440 27) w2) true) (and (distinct w2 w0) true) (and (distinct w2 w1) true))))
 (=> active2 $x355)))
(assert
 (let (($x365 (or (and active3 (or (= a3 (_ bv10 4)) (= b3 (_ bv10 4)))) (and active4 (or (= a4 (_ bv10 4)) (= b4 (_ bv10 4)))))))
 (let (($x366 (not active3)))
 (=> active2 (or $x366 $x365)))))
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
 (let (($x366 (not active3)))
 (=> $x366 (and (= a3 (_ bv10 4)) (= b3 (_ bv10 4)) (not and3)))))
(assert
 (let ((?x400 (ite (= b3 (_ bv7 4)) (_ bv133693440 27) (ite (= b3 (_ bv8 4)) w0 (ite (= b3 (_ bv9 4)) w1 w2)))))
 (let (($x164 (= b3 (_ bv6 4))))
 (let (($x142 (= b3 (_ bv5 4))))
 (let (($x120 (= b3 (_ bv4 4))))
 (let (($x98 (= b3 (_ bv3 4))))
 (let (($x76 (= b3 (_ bv2 4))))
 (let ((?x405 (ite $x76 (_ bv54661252 27) (ite $x98 (_ bv25436424 27) (ite $x120 (_ bv67109360 27) (ite $x142 (_ bv100679168 27) (ite $x164 (_ bv101171200 27) ?x400)))))))
 (let (($x54 (= b3 (_ bv1 4))))
 (let ((?x408 (ite (= b3 (_ bv0 4)) (_ bv118522913 27) (ite $x54 (_ bv52496450 27) ?x405))))
 (let ((?x388 (ite (= a3 (_ bv7 4)) (_ bv133693440 27) (ite (= a3 (_ bv8 4)) w0 (ite (= a3 (_ bv9 4)) w1 w2)))))
 (let (($x163 (= a3 (_ bv6 4))))
 (let (($x141 (= a3 (_ bv5 4))))
 (let (($x119 (= a3 (_ bv4 4))))
 (let (($x97 (= a3 (_ bv3 4))))
 (let (($x75 (= a3 (_ bv2 4))))
 (let ((?x393 (ite $x75 (_ bv54661252 27) (ite $x97 (_ bv25436424 27) (ite $x119 (_ bv67109360 27) (ite $x141 (_ bv100679168 27) (ite $x163 (_ bv101171200 27) ?x388)))))))
 (let (($x53 (= a3 (_ bv1 4))))
 (let ((?x396 (ite (= a3 (_ bv0 4)) (_ bv118522913 27) (ite $x53 (_ bv52496450 27) ?x393))))
 (= w3 (ite and3 (bvand ?x396 ?x408) (bvor ?x396 ?x408))))))))))))))))))))))
(assert
 (let (($x424 (and (and (distinct (_ bv118522913 27) w3) true) (and (distinct (_ bv52496450 27) w3) true) (and (distinct (_ bv54661252 27) w3) true) (and (distinct (_ bv25436424 27) w3) true) (and (distinct (_ bv67109360 27) w3) true) (and (distinct (_ bv100679168 27) w3) true) (and (distinct (_ bv101171200 27) w3) true) (and (distinct (_ bv133693440 27) w3) true) (and (distinct w3 w0) true) (and (distinct w3 w1) true) (and (distinct w3 w2) true))))
 (=> active3 $x424)))
(assert
 (let (($x430 (or (and active4 (or (= a4 (_ bv11 4)) (= b4 (_ bv11 4)))))))
 (let (($x431 (not active4)))
 (=> active3 (or $x431 $x430)))))
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
 (let (($x431 (not active4)))
 (=> $x431 (and (= a4 (_ bv11 4)) (= b4 (_ bv11 4)) (not and4)))))
(assert
 (let (($x229 (= b4 (_ bv8 4))))
 (let ((?x465 (ite $x229 w0 (ite (= b4 (_ bv9 4)) w1 (ite (= b4 (_ bv10 4)) w2 w3)))))
 (let (($x168 (= b4 (_ bv6 4))))
 (let (($x146 (= b4 (_ bv5 4))))
 (let (($x124 (= b4 (_ bv4 4))))
 (let ((?x470 (ite $x124 (_ bv67109360 27) (ite $x146 (_ bv100679168 27) (ite $x168 (_ bv101171200 27) (ite (= b4 (_ bv7 4)) (_ bv133693440 27) ?x465))))))
 (let (($x102 (= b4 (_ bv3 4))))
 (let (($x80 (= b4 (_ bv2 4))))
 (let (($x58 (= b4 (_ bv1 4))))
 (let ((?x475 (ite (= b4 (_ bv0 4)) (_ bv118522913 27) (ite $x58 (_ bv52496450 27) (ite $x80 (_ bv54661252 27) (ite $x102 (_ bv25436424 27) ?x470))))))
 (let (($x228 (= a4 (_ bv8 4))))
 (let ((?x452 (ite $x228 w0 (ite (= a4 (_ bv9 4)) w1 (ite (= a4 (_ bv10 4)) w2 w3)))))
 (let (($x167 (= a4 (_ bv6 4))))
 (let (($x145 (= a4 (_ bv5 4))))
 (let (($x123 (= a4 (_ bv4 4))))
 (let ((?x457 (ite $x123 (_ bv67109360 27) (ite $x145 (_ bv100679168 27) (ite $x167 (_ bv101171200 27) (ite (= a4 (_ bv7 4)) (_ bv133693440 27) ?x452))))))
 (let (($x101 (= a4 (_ bv3 4))))
 (let (($x79 (= a4 (_ bv2 4))))
 (let (($x57 (= a4 (_ bv1 4))))
 (let ((?x462 (ite (= a4 (_ bv0 4)) (_ bv118522913 27) (ite $x57 (_ bv52496450 27) (ite $x79 (_ bv54661252 27) (ite $x101 (_ bv25436424 27) ?x457))))))
 (= w4 (ite and4 (bvand ?x462 ?x475) (bvor ?x462 ?x475))))))))))))))))))))))))
(assert
 (let (($x492 (and (and (distinct (_ bv118522913 27) w4) true) (and (distinct (_ bv52496450 27) w4) true) (and (distinct (_ bv54661252 27) w4) true) (and (distinct (_ bv25436424 27) w4) true) (and (distinct (_ bv67109360 27) w4) true) (and (distinct (_ bv100679168 27) w4) true) (and (distinct (_ bv101171200 27) w4) true) (and (distinct (_ bv133693440 27) w4) true) (and (distinct w4 w0) true) (and (distinct w4 w1) true) (and (distinct w4 w2) true) (and (distinct w4 w3) true))))
 (=> active4 $x492)))
(assert
 (let (($x504 (and (= a0 a1) (or (bvult b0 b1) (and (= b0 b1) (or and0 (not and1)))))))
 (=> (and active0 active1 (and (distinct a1 (_ bv8 4)) true) (and (distinct b1 (_ bv8 4)) true)) (or (bvult a0 a1) $x504))))
(assert
 (let (($x517 (and (= a1 a2) (or (bvult b1 b2) (and (= b1 b2) (or and1 (not and2)))))))
 (=> (and active1 active2 (and (distinct a2 (_ bv9 4)) true) (and (distinct b2 (_ bv9 4)) true)) (or (bvult a1 a2) $x517))))
(assert
 (let (($x530 (and (= a2 a3) (or (bvult b2 b3) (and (= b2 b3) (or and2 (not and3)))))))
 (=> (and active2 active3 (and (distinct a3 (_ bv10 4)) true) (and (distinct b3 (_ bv10 4)) true)) (or (bvult a2 a3) $x530))))
(assert
 (let (($x543 (and (= a3 a4) (or (bvult b3 b4) (and (= b3 b4) (or and3 (not and4)))))))
 (let (($x544 (or (bvult a3 a4) $x543)))
 (let (($x535 (and active3 active4 (and (distinct a4 (_ bv11 4)) true) (and (distinct b4 (_ bv11 4)) true))))
 (=> $x535 $x544)))))
(assert
 (let (($x108 (= b0 (_ bv4 4))))
 (let (($x85 (= a0 (_ bv3 4))))
 (let (($x556 (and $x85 $x108)))
 (let (($x130 (= b0 (_ bv5 4))))
 (let (($x41 (= a0 (_ bv1 4))))
 (let (($x555 (and $x41 $x130)))
 (let (($x554 (and $x41 $x108)))
 (let (($x86 (= b0 (_ bv3 4))))
 (let (($x553 (and $x41 $x86)))
 (let (($x64 (= b0 (_ bv2 4))))
 (let (($x552 (and $x41 $x64)))
 (let (($x192 (= a0 (_ bv0 4))))
 (let (($x551 (and $x192 (= b0 (_ bv7 4)))))
 (let (($x549 (and $x192 $x130)))
 (let (($x548 (and $x192 $x108)))
 (let (($x547 (and $x192 $x86)))
 (let (($x42 (= b0 (_ bv1 4))))
 (let (($x546 (and $x192 $x42)))
 (or $x546 $x547 $x548 $x549 $x551 $x552 $x553 $x554 $x555 $x556))))))))))))))))))))
(assert
 (= w4 (_ bv270784 27)))
(check-sat)
