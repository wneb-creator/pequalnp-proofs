; benchmark generated from python API
(set-info :status unknown)
(declare-fun a0 () (_ BitVec 4))
(declare-fun b0 () (_ BitVec 4))
(declare-fun or0 () Bool)
(declare-fun g0 () (_ BitVec 6))
(declare-fun a1 () (_ BitVec 4))
(declare-fun b1 () (_ BitVec 4))
(declare-fun or1 () Bool)
(declare-fun g1 () (_ BitVec 6))
(declare-fun a2 () (_ BitVec 4))
(declare-fun b2 () (_ BitVec 4))
(declare-fun or2 () Bool)
(declare-fun g2 () (_ BitVec 6))
(declare-fun a3 () (_ BitVec 4))
(declare-fun b3 () (_ BitVec 4))
(declare-fun or3 () Bool)
(declare-fun g3 () (_ BitVec 6))
(declare-fun ta0 () (_ BitVec 4))
(declare-fun tb0 () (_ BitVec 4))
(declare-fun tg0 () (_ BitVec 6))
(assert
 (bvult a0 (_ bv4 4)))
(assert
 (bvult b0 (_ bv4 4)))
(assert
 (bvule a0 b0))
(assert
 (let (($x32 (= b0 (_ bv0 4))))
 (let ((?x33 (ite $x32 (_ bv11 6) (ite (= b0 (_ bv1 4)) (_ bv21 6) (ite (= b0 (_ bv2 4)) (_ bv38 6) (_ bv56 6))))))
 (let (($x26 (= a0 (_ bv0 4))))
 (let ((?x27 (ite $x26 (_ bv11 6) (ite (= a0 (_ bv1 4)) (_ bv21 6) (ite (= a0 (_ bv2 4)) (_ bv38 6) (_ bv56 6))))))
 (= g0 (ite or0 (bvor ?x27 ?x33) (bvand ?x27 ?x33))))))))
(assert
 (and (distinct (bvand g0 (_ bv26 6)) (_ bv0 6)) true))
(assert
 (and (distinct g0 (_ bv0 6)) true))
(assert
 (and (distinct g0 (_ bv63 6)) true))
(assert
 (and (distinct (_ bv11 6) g0) true))
(assert
 (and (distinct (_ bv21 6) g0) true))
(assert
 (and (distinct (_ bv38 6) g0) true))
(assert
 (and (distinct (_ bv56 6) g0) true))
(assert
 (bvult a1 (_ bv5 4)))
(assert
 (bvult b1 (_ bv5 4)))
(assert
 (bvule a1 b1))
(assert
 (let (($x70 (= b1 (_ bv1 4))))
 (let ((?x71 (ite $x70 (_ bv21 6) (ite (= b1 (_ bv2 4)) (_ bv38 6) (ite (= b1 (_ bv3 4)) (_ bv56 6) g0)))))
 (let (($x72 (= b1 (_ bv0 4))))
 (let ((?x73 (ite $x72 (_ bv11 6) ?x71)))
 (let (($x62 (= a1 (_ bv1 4))))
 (let ((?x63 (ite $x62 (_ bv21 6) (ite (= a1 (_ bv2 4)) (_ bv38 6) (ite (= a1 (_ bv3 4)) (_ bv56 6) g0)))))
 (let (($x64 (= a1 (_ bv0 4))))
 (let ((?x65 (ite $x64 (_ bv11 6) ?x63)))
 (= g1 (ite or1 (bvor ?x65 ?x73) (bvand ?x65 ?x73))))))))))))
(assert
 (and (distinct (bvand g1 (_ bv26 6)) (_ bv0 6)) true))
(assert
 (and (distinct g1 (_ bv0 6)) true))
(assert
 (and (distinct g1 (_ bv63 6)) true))
(assert
 (and (distinct (_ bv11 6) g1) true))
(assert
 (and (distinct (_ bv21 6) g1) true))
(assert
 (and (distinct (_ bv38 6) g1) true))
(assert
 (and (distinct (_ bv56 6) g1) true))
(assert
 (and (distinct g1 g0) true))
(assert
 (bvult a2 (_ bv6 4)))
(assert
 (bvult b2 (_ bv6 4)))
(assert
 (bvule a2 b2))
(assert
 (let (($x109 (= b2 (_ bv2 4))))
 (let ((?x110 (ite $x109 (_ bv38 6) (ite (= b2 (_ bv3 4)) (_ bv56 6) (ite (= b2 (_ bv4 4)) g0 g1)))))
 (let (($x111 (= b2 (_ bv1 4))))
 (let (($x113 (= b2 (_ bv0 4))))
 (let ((?x114 (ite $x113 (_ bv11 6) (ite $x111 (_ bv21 6) ?x110))))
 (let (($x99 (= a2 (_ bv2 4))))
 (let ((?x100 (ite $x99 (_ bv38 6) (ite (= a2 (_ bv3 4)) (_ bv56 6) (ite (= a2 (_ bv4 4)) g0 g1)))))
 (let (($x101 (= a2 (_ bv1 4))))
 (let (($x103 (= a2 (_ bv0 4))))
 (let ((?x104 (ite $x103 (_ bv11 6) (ite $x101 (_ bv21 6) ?x100))))
 (= g2 (ite or2 (bvor ?x104 ?x114) (bvand ?x104 ?x114))))))))))))))
(assert
 (and (distinct (bvand g2 (_ bv26 6)) (_ bv0 6)) true))
(assert
 (and (distinct g2 (_ bv0 6)) true))
(assert
 (and (distinct g2 (_ bv63 6)) true))
(assert
 (and (distinct (_ bv11 6) g2) true))
(assert
 (and (distinct (_ bv21 6) g2) true))
(assert
 (and (distinct (_ bv38 6) g2) true))
(assert
 (and (distinct (_ bv56 6) g2) true))
(assert
 (and (distinct g2 g0) true))
(assert
 (and (distinct g2 g1) true))
(assert
 (bvult a3 (_ bv7 4)))
(assert
 (bvult b3 (_ bv7 4)))
(assert
 (bvule a3 b3))
(assert
 (let (($x153 (= b3 (_ bv3 4))))
 (let ((?x154 (ite $x153 (_ bv56 6) (ite (= b3 (_ bv4 4)) g0 (ite (= b3 (_ bv5 4)) g1 g2)))))
 (let (($x155 (= b3 (_ bv2 4))))
 (let (($x157 (= b3 (_ bv1 4))))
 (let (($x159 (= b3 (_ bv0 4))))
 (let ((?x160 (ite $x159 (_ bv11 6) (ite $x157 (_ bv21 6) (ite $x155 (_ bv38 6) ?x154)))))
 (let (($x141 (= a3 (_ bv3 4))))
 (let ((?x142 (ite $x141 (_ bv56 6) (ite (= a3 (_ bv4 4)) g0 (ite (= a3 (_ bv5 4)) g1 g2)))))
 (let (($x143 (= a3 (_ bv2 4))))
 (let (($x145 (= a3 (_ bv1 4))))
 (let (($x147 (= a3 (_ bv0 4))))
 (let ((?x148 (ite $x147 (_ bv11 6) (ite $x145 (_ bv21 6) (ite $x143 (_ bv38 6) ?x142)))))
 (= g3 (ite or3 (bvor ?x148 ?x160) (bvand ?x148 ?x160))))))))))))))))
(assert
 (and (distinct (bvand g3 (_ bv26 6)) (_ bv0 6)) true))
(assert
 (and (distinct g3 (_ bv0 6)) true))
(assert
 (and (distinct g3 (_ bv63 6)) true))
(assert
 (and (distinct (_ bv11 6) g3) true))
(assert
 (and (distinct (_ bv21 6) g3) true))
(assert
 (and (distinct (_ bv38 6) g3) true))
(assert
 (and (distinct (_ bv56 6) g3) true))
(assert
 (and (distinct g3 g0) true))
(assert
 (and (distinct g3 g1) true))
(assert
 (and (distinct g3 g2) true))
(assert
 ((_ pbeq 1 1 1 1 1) (not or0) (not or1) (not or2) (not or3)))
(assert
 (let ((?x183 (concat (concat (ite or1 (_ bv0 1) (_ bv1 1)) a1) b1)))
 (or (= a1 (_ bv4 4)) (= b1 (_ bv4 4)) (bvule (concat (concat (ite or0 (_ bv0 1) (_ bv1 1)) a0) b0) ?x183))))
(assert
 (let ((?x193 (concat (concat (ite or2 (_ bv0 1) (_ bv1 1)) a2) b2)))
 (let ((?x183 (concat (concat (ite or1 (_ bv0 1) (_ bv1 1)) a1) b1)))
 (or (= a2 (_ bv5 4)) (= b2 (_ bv5 4)) (bvule ?x183 ?x193)))))
(assert
 (let ((?x200 (concat (concat (ite or3 (_ bv0 1) (_ bv1 1)) a3) b3)))
 (let ((?x193 (concat (concat (ite or2 (_ bv0 1) (_ bv1 1)) a2) b2)))
 (or (= a3 (_ bv6 4)) (= b3 (_ bv6 4)) (bvule ?x193 ?x200)))))
(assert
 (bvult ta0 (_ bv8 4)))
(assert
 (bvult tb0 (_ bv8 4)))
(assert
 (bvule ta0 tb0))
(assert
 (let (($x230 (= tb0 (_ bv4 4))))
 (let ((?x231 (ite $x230 g0 (ite (= tb0 (_ bv5 4)) g1 (ite (= tb0 (_ bv6 4)) g2 g3)))))
 (let (($x232 (= tb0 (_ bv3 4))))
 (let (($x234 (= tb0 (_ bv2 4))))
 (let (($x236 (= tb0 (_ bv1 4))))
 (let (($x238 (= tb0 (_ bv0 4))))
 (let (($x216 (= ta0 (_ bv4 4))))
 (let ((?x217 (ite $x216 g0 (ite (= ta0 (_ bv5 4)) g1 (ite (= ta0 (_ bv6 4)) g2 g3)))))
 (let (($x218 (= ta0 (_ bv3 4))))
 (let (($x220 (= ta0 (_ bv2 4))))
 (let (($x222 (= ta0 (_ bv1 4))))
 (let (($x224 (= ta0 (_ bv0 4))))
 (let ((?x240 (bvand (ite $x224 (_ bv11 6) (ite $x222 (_ bv21 6) (ite $x220 (_ bv38 6) (ite $x218 (_ bv56 6) ?x217)))) (ite $x238 (_ bv11 6) (ite $x236 (_ bv21 6) (ite $x234 (_ bv38 6) (ite $x232 (_ bv56 6) ?x231)))))))
 (= tg0 ?x240)))))))))))))))
(assert
 (= (bvand tg0 (_ bv26 6)) (_ bv0 6)))
(assert
 (= (bvor (_ bv0 6) tg0) (_ bv37 6)))
(assert
 (and (distinct (bvand tg0 (bvnot (_ bv0 6))) (_ bv0 6)) true))
(assert
 (let (($x70 (= b1 (_ bv1 4))))
 (let ((?x256 (ite $x70 (_ bv21 6) (ite (= b1 (_ bv2 4)) (_ bv38 6) (ite (= b1 (_ bv3 4)) (_ bv56 6) (_ bv0 6))))))
 (let (($x72 (= b1 (_ bv0 4))))
 (let ((?x257 (ite $x72 (_ bv11 6) ?x256)))
 (let (($x62 (= a1 (_ bv1 4))))
 (let ((?x252 (ite $x62 (_ bv21 6) (ite (= a1 (_ bv2 4)) (_ bv38 6) (ite (= a1 (_ bv3 4)) (_ bv56 6) (_ bv0 6))))))
 (let (($x64 (= a1 (_ bv0 4))))
 (let ((?x253 (ite $x64 (_ bv11 6) ?x252)))
 (let ((?x260 (ite or1 (bvor ?x253 ?x257) (bvand ?x253 ?x257))))
 (let (($x105 (= b2 (_ bv4 4))))
 (let (($x107 (= b2 (_ bv3 4))))
 (let (($x109 (= b2 (_ bv2 4))))
 (let (($x111 (= b2 (_ bv1 4))))
 (let (($x113 (= b2 (_ bv0 4))))
 (let ((?x270 (ite $x113 (_ bv11 6) (ite $x111 (_ bv21 6) (ite $x109 (_ bv38 6) (ite $x107 (_ bv56 6) (ite $x105 (_ bv0 6) ?x260)))))))
 (let (($x99 (= a2 (_ bv2 4))))
 (let ((?x263 (ite $x99 (_ bv38 6) (ite (= a2 (_ bv3 4)) (_ bv56 6) (ite (= a2 (_ bv4 4)) (_ bv0 6) ?x260)))))
 (let (($x101 (= a2 (_ bv1 4))))
 (let (($x103 (= a2 (_ bv0 4))))
 (let ((?x265 (ite $x103 (_ bv11 6) (ite $x101 (_ bv21 6) ?x263))))
 (let ((?x273 (ite or2 (bvor ?x265 ?x270) (bvand ?x265 ?x270))))
 (let (($x149 (= b3 (_ bv5 4))))
 (let (($x151 (= b3 (_ bv4 4))))
 (let (($x153 (= b3 (_ bv3 4))))
 (let (($x155 (= b3 (_ bv2 4))))
 (let (($x157 (= b3 (_ bv1 4))))
 (let ((?x284 (ite $x157 (_ bv21 6) (ite $x155 (_ bv38 6) (ite $x153 (_ bv56 6) (ite $x151 (_ bv0 6) (ite $x149 ?x260 ?x273)))))))
 (let (($x159 (= b3 (_ bv0 4))))
 (let ((?x285 (ite $x159 (_ bv11 6) ?x284)))
 (let (($x141 (= a3 (_ bv3 4))))
 (let ((?x276 (ite $x141 (_ bv56 6) (ite (= a3 (_ bv4 4)) (_ bv0 6) (ite (= a3 (_ bv5 4)) ?x260 ?x273)))))
 (let (($x143 (= a3 (_ bv2 4))))
 (let (($x145 (= a3 (_ bv1 4))))
 (let (($x147 (= a3 (_ bv0 4))))
 (let ((?x279 (ite $x147 (_ bv11 6) (ite $x145 (_ bv21 6) (ite $x143 (_ bv38 6) ?x276)))))
 (let ((?x288 (ite or3 (bvor ?x279 ?x285) (bvand ?x279 ?x285))))
 (let (($x226 (= tb0 (_ bv6 4))))
 (let (($x228 (= tb0 (_ bv5 4))))
 (let (($x230 (= tb0 (_ bv4 4))))
 (let (($x232 (= tb0 (_ bv3 4))))
 (let (($x234 (= tb0 (_ bv2 4))))
 (let ((?x300 (ite $x234 (_ bv38 6) (ite $x232 (_ bv56 6) (ite $x230 (_ bv0 6) (ite $x228 ?x260 (ite $x226 ?x273 ?x288)))))))
 (let (($x236 (= tb0 (_ bv1 4))))
 (let (($x238 (= tb0 (_ bv0 4))))
 (let (($x216 (= ta0 (_ bv4 4))))
 (let ((?x291 (ite $x216 (_ bv0 6) (ite (= ta0 (_ bv5 4)) ?x260 (ite (= ta0 (_ bv6 4)) ?x273 ?x288)))))
 (let (($x218 (= ta0 (_ bv3 4))))
 (let (($x220 (= ta0 (_ bv2 4))))
 (let (($x222 (= ta0 (_ bv1 4))))
 (let (($x224 (= ta0 (_ bv0 4))))
 (let ((?x303 (bvand (ite $x224 (_ bv11 6) (ite $x222 (_ bv21 6) (ite $x220 (_ bv38 6) (ite $x218 (_ bv56 6) ?x291)))) (ite $x238 (_ bv11 6) (ite $x236 (_ bv21 6) ?x300)))))
 (and (distinct (bvor (_ bv0 6) ?x303) (_ bv37 6)) true)))))))))))))))))))))))))))))))))))))))))))))))))))))
(assert
 (let (($x109 (= b2 (_ bv2 4))))
 (let ((?x313 (ite $x109 (_ bv38 6) (ite (= b2 (_ bv3 4)) (_ bv56 6) (ite (= b2 (_ bv4 4)) g0 (_ bv0 6))))))
 (let (($x111 (= b2 (_ bv1 4))))
 (let (($x113 (= b2 (_ bv0 4))))
 (let ((?x315 (ite $x113 (_ bv11 6) (ite $x111 (_ bv21 6) ?x313))))
 (let (($x99 (= a2 (_ bv2 4))))
 (let ((?x308 (ite $x99 (_ bv38 6) (ite (= a2 (_ bv3 4)) (_ bv56 6) (ite (= a2 (_ bv4 4)) g0 (_ bv0 6))))))
 (let (($x101 (= a2 (_ bv1 4))))
 (let (($x103 (= a2 (_ bv0 4))))
 (let ((?x310 (ite $x103 (_ bv11 6) (ite $x101 (_ bv21 6) ?x308))))
 (let ((?x318 (ite or2 (bvor ?x310 ?x315) (bvand ?x310 ?x315))))
 (let (($x149 (= b3 (_ bv5 4))))
 (let (($x151 (= b3 (_ bv4 4))))
 (let (($x153 (= b3 (_ bv3 4))))
 (let (($x155 (= b3 (_ bv2 4))))
 (let (($x157 (= b3 (_ bv1 4))))
 (let ((?x329 (ite $x157 (_ bv21 6) (ite $x155 (_ bv38 6) (ite $x153 (_ bv56 6) (ite $x151 g0 (ite $x149 (_ bv0 6) ?x318)))))))
 (let (($x159 (= b3 (_ bv0 4))))
 (let ((?x330 (ite $x159 (_ bv11 6) ?x329)))
 (let (($x141 (= a3 (_ bv3 4))))
 (let ((?x321 (ite $x141 (_ bv56 6) (ite (= a3 (_ bv4 4)) g0 (ite (= a3 (_ bv5 4)) (_ bv0 6) ?x318)))))
 (let (($x143 (= a3 (_ bv2 4))))
 (let (($x145 (= a3 (_ bv1 4))))
 (let (($x147 (= a3 (_ bv0 4))))
 (let ((?x324 (ite $x147 (_ bv11 6) (ite $x145 (_ bv21 6) (ite $x143 (_ bv38 6) ?x321)))))
 (let ((?x333 (ite or3 (bvor ?x324 ?x330) (bvand ?x324 ?x330))))
 (let (($x226 (= tb0 (_ bv6 4))))
 (let (($x228 (= tb0 (_ bv5 4))))
 (let (($x230 (= tb0 (_ bv4 4))))
 (let (($x232 (= tb0 (_ bv3 4))))
 (let (($x234 (= tb0 (_ bv2 4))))
 (let ((?x345 (ite $x234 (_ bv38 6) (ite $x232 (_ bv56 6) (ite $x230 g0 (ite $x228 (_ bv0 6) (ite $x226 ?x318 ?x333)))))))
 (let (($x236 (= tb0 (_ bv1 4))))
 (let (($x238 (= tb0 (_ bv0 4))))
 (let (($x216 (= ta0 (_ bv4 4))))
 (let ((?x336 (ite $x216 g0 (ite (= ta0 (_ bv5 4)) (_ bv0 6) (ite (= ta0 (_ bv6 4)) ?x318 ?x333)))))
 (let (($x218 (= ta0 (_ bv3 4))))
 (let (($x220 (= ta0 (_ bv2 4))))
 (let (($x222 (= ta0 (_ bv1 4))))
 (let (($x224 (= ta0 (_ bv0 4))))
 (let ((?x348 (bvand (ite $x224 (_ bv11 6) (ite $x222 (_ bv21 6) (ite $x220 (_ bv38 6) (ite $x218 (_ bv56 6) ?x336)))) (ite $x238 (_ bv11 6) (ite $x236 (_ bv21 6) ?x345)))))
 (and (distinct (bvor (_ bv0 6) ?x348) (_ bv37 6)) true)))))))))))))))))))))))))))))))))))))))))))
(assert
 (let (($x153 (= b3 (_ bv3 4))))
 (let ((?x359 (ite $x153 (_ bv56 6) (ite (= b3 (_ bv4 4)) g0 (ite (= b3 (_ bv5 4)) g1 (_ bv0 6))))))
 (let (($x155 (= b3 (_ bv2 4))))
 (let (($x157 (= b3 (_ bv1 4))))
 (let (($x159 (= b3 (_ bv0 4))))
 (let ((?x362 (ite $x159 (_ bv11 6) (ite $x157 (_ bv21 6) (ite $x155 (_ bv38 6) ?x359)))))
 (let (($x141 (= a3 (_ bv3 4))))
 (let ((?x353 (ite $x141 (_ bv56 6) (ite (= a3 (_ bv4 4)) g0 (ite (= a3 (_ bv5 4)) g1 (_ bv0 6))))))
 (let (($x143 (= a3 (_ bv2 4))))
 (let (($x145 (= a3 (_ bv1 4))))
 (let (($x147 (= a3 (_ bv0 4))))
 (let ((?x356 (ite $x147 (_ bv11 6) (ite $x145 (_ bv21 6) (ite $x143 (_ bv38 6) ?x353)))))
 (let ((?x365 (ite or3 (bvor ?x356 ?x362) (bvand ?x356 ?x362))))
 (let (($x226 (= tb0 (_ bv6 4))))
 (let (($x228 (= tb0 (_ bv5 4))))
 (let (($x230 (= tb0 (_ bv4 4))))
 (let (($x232 (= tb0 (_ bv3 4))))
 (let (($x234 (= tb0 (_ bv2 4))))
 (let ((?x377 (ite $x234 (_ bv38 6) (ite $x232 (_ bv56 6) (ite $x230 g0 (ite $x228 g1 (ite $x226 (_ bv0 6) ?x365)))))))
 (let (($x236 (= tb0 (_ bv1 4))))
 (let (($x238 (= tb0 (_ bv0 4))))
 (let (($x216 (= ta0 (_ bv4 4))))
 (let ((?x368 (ite $x216 g0 (ite (= ta0 (_ bv5 4)) g1 (ite (= ta0 (_ bv6 4)) (_ bv0 6) ?x365)))))
 (let (($x218 (= ta0 (_ bv3 4))))
 (let (($x220 (= ta0 (_ bv2 4))))
 (let (($x222 (= ta0 (_ bv1 4))))
 (let (($x224 (= ta0 (_ bv0 4))))
 (let ((?x380 (bvand (ite $x224 (_ bv11 6) (ite $x222 (_ bv21 6) (ite $x220 (_ bv38 6) (ite $x218 (_ bv56 6) ?x368)))) (ite $x238 (_ bv11 6) (ite $x236 (_ bv21 6) ?x377)))))
 (and (distinct (bvor (_ bv0 6) ?x380) (_ bv37 6)) true))))))))))))))))))))))))))))))
(assert
 (let (($x230 (= tb0 (_ bv4 4))))
 (let ((?x392 (ite $x230 g0 (ite (= tb0 (_ bv5 4)) g1 (ite (= tb0 (_ bv6 4)) g2 (_ bv0 6))))))
 (let (($x232 (= tb0 (_ bv3 4))))
 (let (($x234 (= tb0 (_ bv2 4))))
 (let (($x236 (= tb0 (_ bv1 4))))
 (let (($x238 (= tb0 (_ bv0 4))))
 (let (($x216 (= ta0 (_ bv4 4))))
 (let ((?x385 (ite $x216 g0 (ite (= ta0 (_ bv5 4)) g1 (ite (= ta0 (_ bv6 4)) g2 (_ bv0 6))))))
 (let (($x218 (= ta0 (_ bv3 4))))
 (let (($x220 (= ta0 (_ bv2 4))))
 (let (($x222 (= ta0 (_ bv1 4))))
 (let (($x224 (= ta0 (_ bv0 4))))
 (let ((?x397 (bvand (ite $x224 (_ bv11 6) (ite $x222 (_ bv21 6) (ite $x220 (_ bv38 6) (ite $x218 (_ bv56 6) ?x385)))) (ite $x238 (_ bv11 6) (ite $x236 (_ bv21 6) (ite $x234 (_ bv38 6) (ite $x232 (_ bv56 6) ?x392)))))))
 (and (distinct (bvor (_ bv0 6) ?x397) (_ bv37 6)) true)))))))))))))))
(assert
 (or (and (= a0 (_ bv0 4)) (= b0 (_ bv0 4))) (and (= a0 (_ bv0 4)) (= b0 (_ bv1 4))) (and (= a0 (_ bv0 4)) (= b0 (_ bv2 4))) (and (= a0 (_ bv0 4)) (= b0 (_ bv3 4))) (and (= a0 (_ bv1 4)) (= b0 (_ bv1 4))) (and (= a0 (_ bv1 4)) (= b0 (_ bv2 4)))))
(check-sat)
