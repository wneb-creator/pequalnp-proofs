; benchmark generated from python API
(set-info :status unknown)
(declare-fun a0 () (_ BitVec 4))
(declare-fun b0 () (_ BitVec 4))
(declare-fun or0 () Bool)
(declare-fun g0 () (_ BitVec 6))
(declare-fun below0 () Bool)
(declare-fun a1 () (_ BitVec 4))
(declare-fun b1 () (_ BitVec 4))
(declare-fun or1 () Bool)
(declare-fun g1 () (_ BitVec 6))
(declare-fun below1 () Bool)
(declare-fun a2 () (_ BitVec 4))
(declare-fun b2 () (_ BitVec 4))
(declare-fun or2 () Bool)
(declare-fun g2 () (_ BitVec 6))
(declare-fun below2 () Bool)
(declare-fun a3 () (_ BitVec 4))
(declare-fun b3 () (_ BitVec 4))
(declare-fun or3 () Bool)
(declare-fun g3 () (_ BitVec 6))
(declare-fun below3 () Bool)
(assert
 (bvult a0 (_ bv4 4)))
(assert
 (bvult b0 (_ bv4 4)))
(assert
 (bvule a0 b0))
(assert
 (let (($x33 (= b0 (_ bv0 4))))
 (let ((?x34 (ite $x33 (_ bv11 6) (ite (= b0 (_ bv1 4)) (_ bv21 6) (ite (= b0 (_ bv2 4)) (_ bv38 6) (_ bv56 6))))))
 (let (($x27 (= a0 (_ bv0 4))))
 (let ((?x28 (ite $x27 (_ bv11 6) (ite (= a0 (_ bv1 4)) (_ bv21 6) (ite (= a0 (_ bv2 4)) (_ bv38 6) (_ bv56 6))))))
 (= g0 (ite or0 (bvor ?x28 ?x34) (bvand ?x28 ?x34))))))))
(assert
 (= below0 (= (bvand g0 (_ bv26 6)) (_ bv0 6))))
(assert
 (let (($x33 (= b0 (_ bv0 4))))
 (let (($x49 (ite $x33 false (ite (= b0 (_ bv1 4)) false (ite (= b0 (_ bv2 4)) false false)))))
 (let (($x27 (= a0 (_ bv0 4))))
 (let (($x46 (ite $x27 false (ite (= a0 (_ bv1 4)) false (ite (= a0 (_ bv2 4)) false false)))))
 (=> or0 (= $x46 $x49)))))))
(assert
 (bvult a1 (_ bv5 4)))
(assert
 (bvult b1 (_ bv5 4)))
(assert
 (bvule a1 b1))
(assert
 (let (($x74 (= b1 (_ bv1 4))))
 (let ((?x75 (ite $x74 (_ bv21 6) (ite (= b1 (_ bv2 4)) (_ bv38 6) (ite (= b1 (_ bv3 4)) (_ bv56 6) g0)))))
 (let (($x76 (= b1 (_ bv0 4))))
 (let ((?x77 (ite $x76 (_ bv11 6) ?x75)))
 (let (($x66 (= a1 (_ bv1 4))))
 (let ((?x67 (ite $x66 (_ bv21 6) (ite (= a1 (_ bv2 4)) (_ bv38 6) (ite (= a1 (_ bv3 4)) (_ bv56 6) g0)))))
 (let (($x68 (= a1 (_ bv0 4))))
 (let ((?x69 (ite $x68 (_ bv11 6) ?x67)))
 (= g1 (ite or1 (bvor ?x69 ?x77) (bvand ?x69 ?x77))))))))))))
(assert
 (= below1 (= (bvand g1 (_ bv26 6)) (_ bv0 6))))
(assert
 (let (($x74 (= b1 (_ bv1 4))))
 (let (($x91 (ite $x74 false (ite (= b1 (_ bv2 4)) false (ite (= b1 (_ bv3 4)) false below0)))))
 (let (($x76 (= b1 (_ bv0 4))))
 (let (($x66 (= a1 (_ bv1 4))))
 (let (($x87 (ite $x66 false (ite (= a1 (_ bv2 4)) false (ite (= a1 (_ bv3 4)) false below0)))))
 (let (($x68 (= a1 (_ bv0 4))))
 (=> or1 (= (ite $x68 false $x87) (ite $x76 false $x91))))))))))
(assert
 (bvult a2 (_ bv6 4)))
(assert
 (bvult b2 (_ bv6 4)))
(assert
 (bvule a2 b2))
(assert
 (let (($x118 (= b2 (_ bv2 4))))
 (let ((?x119 (ite $x118 (_ bv38 6) (ite (= b2 (_ bv3 4)) (_ bv56 6) (ite (= b2 (_ bv4 4)) g0 g1)))))
 (let (($x120 (= b2 (_ bv1 4))))
 (let (($x122 (= b2 (_ bv0 4))))
 (let ((?x123 (ite $x122 (_ bv11 6) (ite $x120 (_ bv21 6) ?x119))))
 (let (($x108 (= a2 (_ bv2 4))))
 (let ((?x109 (ite $x108 (_ bv38 6) (ite (= a2 (_ bv3 4)) (_ bv56 6) (ite (= a2 (_ bv4 4)) g0 g1)))))
 (let (($x110 (= a2 (_ bv1 4))))
 (let (($x112 (= a2 (_ bv0 4))))
 (let ((?x113 (ite $x112 (_ bv11 6) (ite $x110 (_ bv21 6) ?x109))))
 (= g2 (ite or2 (bvor ?x113 ?x123) (bvand ?x113 ?x123))))))))))))))
(assert
 (= below2 (= (bvand g2 (_ bv26 6)) (_ bv0 6))))
(assert
 (let (($x118 (= b2 (_ bv2 4))))
 (let (($x138 (ite $x118 false (ite (= b2 (_ bv3 4)) false (ite (= b2 (_ bv4 4)) below0 below1)))))
 (let (($x120 (= b2 (_ bv1 4))))
 (let (($x122 (= b2 (_ bv0 4))))
 (let (($x108 (= a2 (_ bv2 4))))
 (let (($x133 (ite $x108 false (ite (= a2 (_ bv3 4)) false (ite (= a2 (_ bv4 4)) below0 below1)))))
 (let (($x110 (= a2 (_ bv1 4))))
 (let (($x112 (= a2 (_ bv0 4))))
 (let (($x141 (= (ite $x112 false (ite $x110 false $x133)) (ite $x122 false (ite $x120 false $x138)))))
 (=> or2 $x141)))))))))))
(assert
 (bvult a3 (_ bv7 4)))
(assert
 (bvult b3 (_ bv7 4)))
(assert
 (bvule a3 b3))
(assert
 (let (($x168 (= b3 (_ bv3 4))))
 (let ((?x169 (ite $x168 (_ bv56 6) (ite (= b3 (_ bv4 4)) g0 (ite (= b3 (_ bv5 4)) g1 g2)))))
 (let (($x170 (= b3 (_ bv2 4))))
 (let (($x172 (= b3 (_ bv1 4))))
 (let (($x174 (= b3 (_ bv0 4))))
 (let ((?x175 (ite $x174 (_ bv11 6) (ite $x172 (_ bv21 6) (ite $x170 (_ bv38 6) ?x169)))))
 (let (($x156 (= a3 (_ bv3 4))))
 (let ((?x157 (ite $x156 (_ bv56 6) (ite (= a3 (_ bv4 4)) g0 (ite (= a3 (_ bv5 4)) g1 g2)))))
 (let (($x158 (= a3 (_ bv2 4))))
 (let (($x160 (= a3 (_ bv1 4))))
 (let (($x162 (= a3 (_ bv0 4))))
 (let ((?x163 (ite $x162 (_ bv11 6) (ite $x160 (_ bv21 6) (ite $x158 (_ bv38 6) ?x157)))))
 (= g3 (ite or3 (bvor ?x163 ?x175) (bvand ?x163 ?x175))))))))))))))))
(assert
 (= below3 (= (bvand g3 (_ bv26 6)) (_ bv0 6))))
(assert
 (let (($x168 (= b3 (_ bv3 4))))
 (let (($x191 (ite $x168 false (ite (= b3 (_ bv4 4)) below0 (ite (= b3 (_ bv5 4)) below1 below2)))))
 (let (($x170 (= b3 (_ bv2 4))))
 (let (($x172 (= b3 (_ bv1 4))))
 (let (($x174 (= b3 (_ bv0 4))))
 (let (($x156 (= a3 (_ bv3 4))))
 (let (($x185 (ite $x156 false (ite (= a3 (_ bv4 4)) below0 (ite (= a3 (_ bv5 4)) below1 below2)))))
 (let (($x158 (= a3 (_ bv2 4))))
 (let (($x160 (= a3 (_ bv1 4))))
 (let (($x162 (= a3 (_ bv0 4))))
 (let (($x195 (= (ite $x162 false (ite $x160 false (ite $x158 false $x185))) (ite $x174 false (ite $x172 false (ite $x170 false $x191))))))
 (=> or3 $x195)))))))))))))
(assert
 (= (_ bv37 6) g3))
(assert
 (or (and (not or0) (not below0)) (and (not or1) (not below1)) (and (not or2) (not below2)) (and (not or3) (not below3))))
(assert
 (or (or (= a1 (_ bv4 4)) (= b1 (_ bv4 4))) (or (= a2 (_ bv4 4)) (= b2 (_ bv4 4))) (or (= a3 (_ bv4 4)) (= b3 (_ bv4 4)))))
(assert
 (or (or (= a2 (_ bv5 4)) (= b2 (_ bv5 4))) (or (= a3 (_ bv5 4)) (= b3 (_ bv5 4)))))
(assert
 (or (or (= a3 (_ bv6 4)) (= b3 (_ bv6 4)))))
(assert
 (let ((?x229 (concat (concat (ite or1 (_ bv0 1) (_ bv1 1)) a1) b1)))
 (let (($x213 (= b1 (_ bv4 4))))
 (let (($x212 (= a1 (_ bv4 4))))
 (or $x212 $x213 (bvule (concat (concat (ite or0 (_ bv0 1) (_ bv1 1)) a0) b0) ?x229))))))
(assert
 (let ((?x237 (concat (concat (ite or2 (_ bv0 1) (_ bv1 1)) a2) b2)))
 (let ((?x229 (concat (concat (ite or1 (_ bv0 1) (_ bv1 1)) a1) b1)))
 (let (($x219 (= b2 (_ bv5 4))))
 (let (($x218 (= a2 (_ bv5 4))))
 (or $x218 $x219 (bvule ?x229 ?x237)))))))
(assert
 (let ((?x242 (concat (concat (ite or3 (_ bv0 1) (_ bv1 1)) a3) b3)))
(let ((?x237 (concat (concat (ite or2 (_ bv0 1) (_ bv1 1)) a2) b2)))
(let (($x224 (= b3 (_ bv6 4))))
(let (($x223 (= a3 (_ bv6 4))))
(or $x223 $x224 (bvule ?x237 ?x242)))))))
(check-sat)
