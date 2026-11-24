; benchmark generated from python API
(set-info :status unknown)
(declare-fun active0 () Bool)
(declare-fun b0 () (_ BitVec 4))
(declare-fun a0 () (_ BitVec 4))
(declare-fun and0 () Bool)
(declare-fun w0 () (_ BitVec 27))
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
(assert
 active0)
(assert
 (bvult b0 (_ bv8 4)))
(assert
 (=> active0 (bvult a0 b0)))
(assert
 (let (($x59 (= b0 (_ bv4 4))))
 (let ((?x60 (ite $x59 (_ bv67109360 27) (ite (= b0 (_ bv5 4)) (_ bv100679168 27) (ite (= b0 (_ bv6 4)) (_ bv117948416 27) (_ bv133693440 27))))))
 (let (($x61 (= b0 (_ bv3 4))))
 (let (($x63 (= b0 (_ bv2 4))))
 (let (($x65 (= b0 (_ bv1 4))))
 (let ((?x68 (ite (= b0 (_ bv0 4)) (_ bv118522913 27) (ite $x65 (_ bv119605314 27) (ite $x63 (_ bv54661252 27) (ite $x61 (_ bv25436424 27) ?x60))))))
 (let ((?x42 (ite (= a0 (_ bv4 4)) (_ bv67109360 27) (ite (= a0 (_ bv5 4)) (_ bv100679168 27) (ite (= a0 (_ bv6 4)) (_ bv117948416 27) (_ bv133693440 27))))))
 (let (($x44 (= a0 (_ bv3 4))))
 (let (($x47 (= a0 (_ bv2 4))))
 (let (($x53 (= a0 (_ bv0 4))))
 (let ((?x54 (ite $x53 (_ bv118522913 27) (ite (= a0 (_ bv1 4)) (_ bv119605314 27) (ite $x47 (_ bv54661252 27) (ite $x44 (_ bv25436424 27) ?x42))))))
 (= w0 (ite and0 (bvand ?x54 ?x68) (bvor ?x54 ?x68)))))))))))))))
(assert
 (let (($x81 (and (and (distinct (_ bv118522913 27) w0) true) (and (distinct (_ bv119605314 27) w0) true) (and (distinct (_ bv54661252 27) w0) true) (and (distinct (_ bv25436424 27) w0) true) (and (distinct (_ bv67109360 27) w0) true) (and (distinct (_ bv100679168 27) w0) true) (and (distinct (_ bv117948416 27) w0) true) (and (distinct (_ bv133693440 27) w0) true))))
 (=> active0 $x81)))
(assert
 (let (($x91 (or (and active1 (or (= a1 (_ bv8 4)) (= b1 (_ bv8 4)))) (and active2 (or (= a2 (_ bv8 4)) (= b2 (_ bv8 4)))))))
 (let (($x92 (not active1)))
 (=> active0 (or $x92 $x91)))))
(assert
 (bvult b1 (_ bv9 4)))
(assert
 (=> active1 (bvult a1 b1)))
(assert
 (=> active1 active0))
(assert
 (let (($x92 (not active1)))
 (=> $x92 (and (= a1 (_ bv8 4)) (= b1 (_ bv8 4)) (not and1)))))
(assert
 (let ((?x125 (ite (= b1 (_ bv5 4)) (_ bv100679168 27) (ite (= b1 (_ bv6 4)) (_ bv117948416 27) (ite (= b1 (_ bv7 4)) (_ bv133693440 27) w0)))))
 (let ((?x131 (ite (= b1 (_ bv2 4)) (_ bv54661252 27) (ite (= b1 (_ bv3 4)) (_ bv25436424 27) (ite (= b1 (_ bv4 4)) (_ bv67109360 27) ?x125)))))
 (let ((?x135 (ite (= b1 (_ bv0 4)) (_ bv118522913 27) (ite (= b1 (_ bv1 4)) (_ bv119605314 27) ?x131))))
 (let ((?x109 (ite (= a1 (_ bv5 4)) (_ bv100679168 27) (ite (= a1 (_ bv6 4)) (_ bv117948416 27) (ite (= a1 (_ bv7 4)) (_ bv133693440 27) w0)))))
 (let ((?x115 (ite (= a1 (_ bv2 4)) (_ bv54661252 27) (ite (= a1 (_ bv3 4)) (_ bv25436424 27) (ite (= a1 (_ bv4 4)) (_ bv67109360 27) ?x109)))))
 (let ((?x119 (ite (= a1 (_ bv0 4)) (_ bv118522913 27) (ite (= a1 (_ bv1 4)) (_ bv119605314 27) ?x115))))
 (= w1 (ite and1 (bvand ?x119 ?x135) (bvor ?x119 ?x135))))))))))
(assert
 (let (($x149 (and (and (distinct (_ bv118522913 27) w1) true) (and (distinct (_ bv119605314 27) w1) true) (and (distinct (_ bv54661252 27) w1) true) (and (distinct (_ bv25436424 27) w1) true) (and (distinct (_ bv67109360 27) w1) true) (and (distinct (_ bv100679168 27) w1) true) (and (distinct (_ bv117948416 27) w1) true) (and (distinct (_ bv133693440 27) w1) true) (and (distinct w1 w0) true))))
 (=> active1 $x149)))
(assert
 (let (($x155 (or (and active2 (or (= a2 (_ bv9 4)) (= b2 (_ bv9 4)))))))
 (let (($x156 (not active2)))
 (=> active1 (or $x156 $x155)))))
(assert
 (bvult b2 (_ bv10 4)))
(assert
 (=> active2 (bvult a2 b2)))
(assert
 (=> active2 active1))
(assert
 (let (($x156 (not active2)))
 (=> $x156 (and (= a2 (_ bv9 4)) (= b2 (_ bv9 4)) (not and2)))))
(assert
 (let ((?x188 (ite (= b2 (_ bv6 4)) (_ bv117948416 27) (ite (= b2 (_ bv7 4)) (_ bv133693440 27) (ite (= b2 (_ bv8 4)) w0 w1)))))
 (let ((?x194 (ite (= b2 (_ bv3 4)) (_ bv25436424 27) (ite (= b2 (_ bv4 4)) (_ bv67109360 27) (ite (= b2 (_ bv5 4)) (_ bv100679168 27) ?x188)))))
 (let ((?x200 (ite (= b2 (_ bv0 4)) (_ bv118522913 27) (ite (= b2 (_ bv1 4)) (_ bv119605314 27) (ite (= b2 (_ bv2 4)) (_ bv54661252 27) ?x194)))))
 (let ((?x171 (ite (= a2 (_ bv6 4)) (_ bv117948416 27) (ite (= a2 (_ bv7 4)) (_ bv133693440 27) (ite (= a2 (_ bv8 4)) w0 w1)))))
 (let ((?x177 (ite (= a2 (_ bv3 4)) (_ bv25436424 27) (ite (= a2 (_ bv4 4)) (_ bv67109360 27) (ite (= a2 (_ bv5 4)) (_ bv100679168 27) ?x171)))))
 (let ((?x183 (ite (= a2 (_ bv0 4)) (_ bv118522913 27) (ite (= a2 (_ bv1 4)) (_ bv119605314 27) (ite (= a2 (_ bv2 4)) (_ bv54661252 27) ?x177)))))
 (= w2 (ite and2 (bvand ?x183 ?x200) (bvor ?x183 ?x200))))))))))
(assert
 (let (($x215 (and (and (distinct (_ bv118522913 27) w2) true) (and (distinct (_ bv119605314 27) w2) true) (and (distinct (_ bv54661252 27) w2) true) (and (distinct (_ bv25436424 27) w2) true) (and (distinct (_ bv67109360 27) w2) true) (and (distinct (_ bv100679168 27) w2) true) (and (distinct (_ bv117948416 27) w2) true) (and (distinct (_ bv133693440 27) w2) true) (and (distinct w2 w0) true) (and (distinct w2 w1) true))))
 (=> active2 $x215)))
(assert
 (let (($x227 (and (= a0 a1) (or (bvult b0 b1) (and (= b0 b1) (or and0 (not and1)))))))
 (=> (and active0 active1 (and (distinct a1 (_ bv8 4)) true) (and (distinct b1 (_ bv8 4)) true)) (or (bvult a0 a1) $x227))))
(assert
 (let (($x240 (and (= a1 a2) (or (bvult b1 b2) (and (= b1 b2) (or and1 (not and2)))))))
 (let (($x241 (or (bvult a1 a2) $x240)))
 (let (($x232 (and active1 active2 (and (distinct a2 (_ bv9 4)) true) (and (distinct b2 (_ bv9 4)) true))))
 (=> $x232 $x241)))))
(assert
 (let (($x59 (= b0 (_ bv4 4))))
 (let (($x44 (= a0 (_ bv3 4))))
 (let (($x252 (and $x44 $x59)))
 (let (($x57 (= b0 (_ bv5 4))))
 (let (($x47 (= a0 (_ bv2 4))))
 (let (($x251 (and $x47 $x57)))
 (let (($x250 (and $x47 $x59)))
 (let (($x61 (= b0 (_ bv3 4))))
 (let (($x249 (and $x47 $x61)))
 (let (($x55 (= b0 (_ bv6 4))))
 (let (($x53 (= a0 (_ bv0 4))))
 (let (($x248 (and $x53 $x55)))
 (let (($x247 (and $x53 $x57)))
 (let (($x246 (and $x53 $x59)))
 (let (($x245 (and $x53 $x61)))
 (let (($x63 (= b0 (_ bv2 4))))
 (let (($x244 (and $x53 $x63)))
 (let (($x65 (= b0 (_ bv1 4))))
 (let (($x243 (and $x53 $x65)))
 (or $x243 $x244 $x245 $x246 $x247 $x248 $x249 $x250 $x251 $x252)))))))))))))))))))))
(assert
 (= w2 (_ bv8576 27)))
(check-sat)
