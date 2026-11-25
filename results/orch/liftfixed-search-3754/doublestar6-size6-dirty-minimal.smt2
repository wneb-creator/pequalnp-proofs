; benchmark generated from python API
(set-info :status unknown)
(declare-fun a0 () (_ BitVec 4))
(declare-fun b0 () (_ BitVec 4))
(declare-fun or0 () Bool)
(declare-fun g0 () (_ BitVec 8))
(declare-fun below0 () Bool)
(declare-fun a1 () (_ BitVec 4))
(declare-fun b1 () (_ BitVec 4))
(declare-fun or1 () Bool)
(declare-fun g1 () (_ BitVec 8))
(declare-fun below1 () Bool)
(declare-fun a2 () (_ BitVec 4))
(declare-fun b2 () (_ BitVec 4))
(declare-fun or2 () Bool)
(declare-fun g2 () (_ BitVec 8))
(declare-fun below2 () Bool)
(declare-fun a3 () (_ BitVec 4))
(declare-fun b3 () (_ BitVec 4))
(declare-fun or3 () Bool)
(declare-fun g3 () (_ BitVec 8))
(declare-fun below3 () Bool)
(declare-fun a4 () (_ BitVec 4))
(declare-fun b4 () (_ BitVec 4))
(declare-fun or4 () Bool)
(declare-fun g4 () (_ BitVec 8))
(declare-fun below4 () Bool)
(declare-fun a5 () (_ BitVec 4))
(declare-fun b5 () (_ BitVec 4))
(declare-fun or5 () Bool)
(declare-fun g5 () (_ BitVec 8))
(declare-fun below5 () Bool)
(assert
 (bvult a0 (_ bv6 4)))
(assert
 (bvult b0 (_ bv6 4)))
(assert
 (bvule a0 b0))
(assert
 (let (($x41 (= b0 (_ bv2 4))))
 (let ((?x42 (ite $x41 (_ bv138 8) (ite (= b0 (_ bv3 4)) (_ bv140 8) (ite (= b0 (_ bv4 4)) (_ bv208 8) (_ bv224 8))))))
 (let (($x43 (= b0 (_ bv1 4))))
 (let (($x45 (= b0 (_ bv0 4))))
 (let ((?x46 (ite $x45 (_ bv71 8) (ite $x43 (_ bv57 8) ?x42))))
 (let (($x29 (= a0 (_ bv2 4))))
 (let ((?x30 (ite $x29 (_ bv138 8) (ite (= a0 (_ bv3 4)) (_ bv140 8) (ite (= a0 (_ bv4 4)) (_ bv208 8) (_ bv224 8))))))
 (let (($x32 (= a0 (_ bv1 4))))
 (let (($x35 (= a0 (_ bv0 4))))
 (let ((?x36 (ite $x35 (_ bv71 8) (ite $x32 (_ bv57 8) ?x30))))
 (= g0 (ite or0 (bvor ?x36 ?x46) (bvand ?x36 ?x46))))))))))))))
(assert
 (= below0 (= (bvand g0 (_ bv200 8)) (_ bv0 8))))
(assert
 (let (($x41 (= b0 (_ bv2 4))))
 (let (($x63 (ite $x41 false (ite (= b0 (_ bv3 4)) false (ite (= b0 (_ bv4 4)) false false)))))
 (let (($x43 (= b0 (_ bv1 4))))
 (let (($x45 (= b0 (_ bv0 4))))
 (let (($x29 (= a0 (_ bv2 4))))
 (let (($x58 (ite $x29 false (ite (= a0 (_ bv3 4)) false (ite (= a0 (_ bv4 4)) false false)))))
 (let (($x32 (= a0 (_ bv1 4))))
 (let (($x35 (= a0 (_ bv0 4))))
 (let (($x66 (= (ite $x35 false (ite $x32 false $x58)) (ite $x45 false (ite $x43 false $x63)))))
 (=> or0 $x66)))))))))))
(assert
 (and (distinct g0 (_ bv0 8)) true))
(assert
 (and (distinct g0 (_ bv255 8)) true))
(assert
 (and (distinct (_ bv71 8) g0) true))
(assert
 (and (distinct (_ bv57 8) g0) true))
(assert
 (and (distinct (_ bv138 8) g0) true))
(assert
 (and (distinct (_ bv140 8) g0) true))
(assert
 (and (distinct (_ bv208 8) g0) true))
(assert
 (and (distinct (_ bv224 8) g0) true))
(assert
 (bvult a1 (_ bv7 4)))
(assert
 (bvult b1 (_ bv7 4)))
(assert
 (bvule a1 b1))
(assert
 (let (($x103 (= b1 (_ bv3 4))))
 (let ((?x104 (ite $x103 (_ bv140 8) (ite (= b1 (_ bv4 4)) (_ bv208 8) (ite (= b1 (_ bv5 4)) (_ bv224 8) g0)))))
 (let (($x105 (= b1 (_ bv2 4))))
 (let (($x107 (= b1 (_ bv1 4))))
 (let (($x109 (= b1 (_ bv0 4))))
 (let ((?x110 (ite $x109 (_ bv71 8) (ite $x107 (_ bv57 8) (ite $x105 (_ bv138 8) ?x104)))))
 (let (($x91 (= a1 (_ bv3 4))))
 (let ((?x92 (ite $x91 (_ bv140 8) (ite (= a1 (_ bv4 4)) (_ bv208 8) (ite (= a1 (_ bv5 4)) (_ bv224 8) g0)))))
 (let (($x93 (= a1 (_ bv2 4))))
 (let (($x95 (= a1 (_ bv1 4))))
 (let (($x97 (= a1 (_ bv0 4))))
 (let ((?x98 (ite $x97 (_ bv71 8) (ite $x95 (_ bv57 8) (ite $x93 (_ bv138 8) ?x92)))))
 (= g1 (ite or1 (bvor ?x98 ?x110) (bvand ?x98 ?x110))))))))))))))))
(assert
 (= below1 (= (bvand g1 (_ bv200 8)) (_ bv0 8))))
(assert
 (let (($x103 (= b1 (_ bv3 4))))
 (let (($x126 (ite $x103 false (ite (= b1 (_ bv4 4)) false (ite (= b1 (_ bv5 4)) false below0)))))
 (let (($x105 (= b1 (_ bv2 4))))
 (let (($x107 (= b1 (_ bv1 4))))
 (let (($x109 (= b1 (_ bv0 4))))
 (let (($x91 (= a1 (_ bv3 4))))
 (let (($x120 (ite $x91 false (ite (= a1 (_ bv4 4)) false (ite (= a1 (_ bv5 4)) false below0)))))
 (let (($x93 (= a1 (_ bv2 4))))
 (let (($x95 (= a1 (_ bv1 4))))
 (let (($x97 (= a1 (_ bv0 4))))
 (let (($x130 (= (ite $x97 false (ite $x95 false (ite $x93 false $x120))) (ite $x109 false (ite $x107 false (ite $x105 false $x126))))))
 (=> or1 $x130)))))))))))))
(assert
 (and (distinct g1 (_ bv0 8)) true))
(assert
 (and (distinct g1 (_ bv255 8)) true))
(assert
 (and (distinct (_ bv71 8) g1) true))
(assert
 (and (distinct (_ bv57 8) g1) true))
(assert
 (and (distinct (_ bv138 8) g1) true))
(assert
 (and (distinct (_ bv140 8) g1) true))
(assert
 (and (distinct (_ bv208 8) g1) true))
(assert
 (and (distinct (_ bv224 8) g1) true))
(assert
 (and (distinct g1 g0) true))
(assert
 (bvult a2 (_ bv8 4)))
(assert
 (bvult b2 (_ bv8 4)))
(assert
 (bvule a2 b2))
(assert
 (let (($x168 (= b2 (_ bv4 4))))
 (let ((?x169 (ite $x168 (_ bv208 8) (ite (= b2 (_ bv5 4)) (_ bv224 8) (ite (= b2 (_ bv6 4)) g0 g1)))))
 (let (($x170 (= b2 (_ bv3 4))))
 (let (($x172 (= b2 (_ bv2 4))))
 (let (($x174 (= b2 (_ bv1 4))))
 (let (($x176 (= b2 (_ bv0 4))))
 (let ((?x177 (ite $x176 (_ bv71 8) (ite $x174 (_ bv57 8) (ite $x172 (_ bv138 8) (ite $x170 (_ bv140 8) ?x169))))))
 (let (($x154 (= a2 (_ bv4 4))))
 (let ((?x155 (ite $x154 (_ bv208 8) (ite (= a2 (_ bv5 4)) (_ bv224 8) (ite (= a2 (_ bv6 4)) g0 g1)))))
 (let (($x156 (= a2 (_ bv3 4))))
 (let (($x158 (= a2 (_ bv2 4))))
 (let (($x160 (= a2 (_ bv1 4))))
 (let (($x162 (= a2 (_ bv0 4))))
 (let ((?x163 (ite $x162 (_ bv71 8) (ite $x160 (_ bv57 8) (ite $x158 (_ bv138 8) (ite $x156 (_ bv140 8) ?x155))))))
 (= g2 (ite or2 (bvor ?x163 ?x177) (bvand ?x163 ?x177))))))))))))))))))
(assert
 (= below2 (= (bvand g2 (_ bv200 8)) (_ bv0 8))))
(assert
 (let (($x168 (= b2 (_ bv4 4))))
 (let (($x194 (ite $x168 false (ite (= b2 (_ bv5 4)) false (ite (= b2 (_ bv6 4)) below0 below1)))))
 (let (($x170 (= b2 (_ bv3 4))))
 (let (($x172 (= b2 (_ bv2 4))))
 (let (($x174 (= b2 (_ bv1 4))))
 (let (($x176 (= b2 (_ bv0 4))))
 (let (($x198 (ite $x176 false (ite $x174 false (ite $x172 false (ite $x170 false $x194))))))
 (let (($x154 (= a2 (_ bv4 4))))
 (let (($x187 (ite $x154 false (ite (= a2 (_ bv5 4)) false (ite (= a2 (_ bv6 4)) below0 below1)))))
 (let (($x156 (= a2 (_ bv3 4))))
 (let (($x158 (= a2 (_ bv2 4))))
 (let (($x160 (= a2 (_ bv1 4))))
 (let (($x162 (= a2 (_ bv0 4))))
 (let (($x191 (ite $x162 false (ite $x160 false (ite $x158 false (ite $x156 false $x187))))))
 (=> or2 (= $x191 $x198)))))))))))))))))
(assert
 (and (distinct g2 (_ bv0 8)) true))
(assert
 (and (distinct g2 (_ bv255 8)) true))
(assert
 (and (distinct (_ bv71 8) g2) true))
(assert
 (and (distinct (_ bv57 8) g2) true))
(assert
 (and (distinct (_ bv138 8) g2) true))
(assert
 (and (distinct (_ bv140 8) g2) true))
(assert
 (and (distinct (_ bv208 8) g2) true))
(assert
 (and (distinct (_ bv224 8) g2) true))
(assert
 (and (distinct g2 g0) true))
(assert
 (and (distinct g2 g1) true))
(assert
 (bvult a3 (_ bv9 4)))
(assert
 (bvult b3 (_ bv9 4)))
(assert
 (bvule a3 b3))
(assert
 (let (($x240 (= b3 (_ bv5 4))))
 (let ((?x241 (ite $x240 (_ bv224 8) (ite (= b3 (_ bv6 4)) g0 (ite (= b3 (_ bv7 4)) g1 g2)))))
 (let (($x242 (= b3 (_ bv4 4))))
 (let (($x244 (= b3 (_ bv3 4))))
 (let (($x246 (= b3 (_ bv2 4))))
 (let (($x248 (= b3 (_ bv1 4))))
 (let (($x250 (= b3 (_ bv0 4))))
 (let ((?x251 (ite $x250 (_ bv71 8) (ite $x248 (_ bv57 8) (ite $x246 (_ bv138 8) (ite $x244 (_ bv140 8) (ite $x242 (_ bv208 8) ?x241)))))))
 (let (($x224 (= a3 (_ bv5 4))))
 (let ((?x225 (ite $x224 (_ bv224 8) (ite (= a3 (_ bv6 4)) g0 (ite (= a3 (_ bv7 4)) g1 g2)))))
 (let (($x226 (= a3 (_ bv4 4))))
 (let (($x228 (= a3 (_ bv3 4))))
 (let (($x230 (= a3 (_ bv2 4))))
 (let (($x232 (= a3 (_ bv1 4))))
 (let (($x234 (= a3 (_ bv0 4))))
 (let ((?x235 (ite $x234 (_ bv71 8) (ite $x232 (_ bv57 8) (ite $x230 (_ bv138 8) (ite $x228 (_ bv140 8) (ite $x226 (_ bv208 8) ?x225)))))))
 (= g3 (ite or3 (bvor ?x235 ?x251) (bvand ?x235 ?x251))))))))))))))))))))
(assert
 (= below3 (= (bvand g3 (_ bv200 8)) (_ bv0 8))))
(assert
 (let (($x240 (= b3 (_ bv5 4))))
 (let (($x269 (ite $x240 false (ite (= b3 (_ bv6 4)) below0 (ite (= b3 (_ bv7 4)) below1 below2)))))
 (let (($x242 (= b3 (_ bv4 4))))
 (let (($x244 (= b3 (_ bv3 4))))
 (let (($x246 (= b3 (_ bv2 4))))
 (let (($x248 (= b3 (_ bv1 4))))
 (let (($x273 (ite $x248 false (ite $x246 false (ite $x244 false (ite $x242 false $x269))))))
 (let (($x250 (= b3 (_ bv0 4))))
 (let (($x224 (= a3 (_ bv5 4))))
 (let (($x261 (ite $x224 false (ite (= a3 (_ bv6 4)) below0 (ite (= a3 (_ bv7 4)) below1 below2)))))
 (let (($x226 (= a3 (_ bv4 4))))
 (let (($x228 (= a3 (_ bv3 4))))
 (let (($x230 (= a3 (_ bv2 4))))
 (let (($x232 (= a3 (_ bv1 4))))
 (let (($x265 (ite $x232 false (ite $x230 false (ite $x228 false (ite $x226 false $x261))))))
 (let (($x234 (= a3 (_ bv0 4))))
 (=> or3 (= (ite $x234 false $x265) (ite $x250 false $x273))))))))))))))))))))
(assert
 (and (distinct g3 (_ bv0 8)) true))
(assert
 (and (distinct g3 (_ bv255 8)) true))
(assert
 (and (distinct (_ bv71 8) g3) true))
(assert
 (and (distinct (_ bv57 8) g3) true))
(assert
 (and (distinct (_ bv138 8) g3) true))
(assert
 (and (distinct (_ bv140 8) g3) true))
(assert
 (and (distinct (_ bv208 8) g3) true))
(assert
 (and (distinct (_ bv224 8) g3) true))
(assert
 (and (distinct g3 g0) true))
(assert
 (and (distinct g3 g1) true))
(assert
 (and (distinct g3 g2) true))
(assert
 (bvult a4 (_ bv10 4)))
(assert
 (bvult b4 (_ bv10 4)))
(assert
 (bvule a4 b4))
(assert
 (let (($x319 (= b4 (_ bv6 4))))
 (let ((?x320 (ite $x319 g0 (ite (= b4 (_ bv7 4)) g1 (ite (= b4 (_ bv8 4)) g2 g3)))))
 (let (($x321 (= b4 (_ bv5 4))))
 (let (($x323 (= b4 (_ bv4 4))))
 (let (($x325 (= b4 (_ bv3 4))))
 (let (($x327 (= b4 (_ bv2 4))))
 (let (($x329 (= b4 (_ bv1 4))))
 (let ((?x330 (ite $x329 (_ bv57 8) (ite $x327 (_ bv138 8) (ite $x325 (_ bv140 8) (ite $x323 (_ bv208 8) (ite $x321 (_ bv224 8) ?x320)))))))
 (let (($x331 (= b4 (_ bv0 4))))
 (let ((?x332 (ite $x331 (_ bv71 8) ?x330)))
 (let (($x301 (= a4 (_ bv6 4))))
 (let ((?x302 (ite $x301 g0 (ite (= a4 (_ bv7 4)) g1 (ite (= a4 (_ bv8 4)) g2 g3)))))
 (let (($x303 (= a4 (_ bv5 4))))
 (let (($x305 (= a4 (_ bv4 4))))
 (let (($x307 (= a4 (_ bv3 4))))
 (let (($x309 (= a4 (_ bv2 4))))
 (let (($x311 (= a4 (_ bv1 4))))
 (let ((?x312 (ite $x311 (_ bv57 8) (ite $x309 (_ bv138 8) (ite $x307 (_ bv140 8) (ite $x305 (_ bv208 8) (ite $x303 (_ bv224 8) ?x302)))))))
 (let (($x313 (= a4 (_ bv0 4))))
 (let ((?x314 (ite $x313 (_ bv71 8) ?x312)))
 (= g4 (ite or4 (bvor ?x314 ?x332) (bvand ?x314 ?x332))))))))))))))))))))))))
(assert
 (= below4 (= (bvand g4 (_ bv200 8)) (_ bv0 8))))
(assert
 (let (($x319 (= b4 (_ bv6 4))))
 (let (($x351 (ite $x319 below0 (ite (= b4 (_ bv7 4)) below1 (ite (= b4 (_ bv8 4)) below2 below3)))))
 (let (($x321 (= b4 (_ bv5 4))))
 (let (($x323 (= b4 (_ bv4 4))))
 (let (($x325 (= b4 (_ bv3 4))))
 (let (($x327 (= b4 (_ bv2 4))))
 (let (($x355 (ite $x327 false (ite $x325 false (ite $x323 false (ite $x321 false $x351))))))
 (let (($x329 (= b4 (_ bv1 4))))
 (let (($x331 (= b4 (_ bv0 4))))
 (let (($x301 (= a4 (_ bv6 4))))
 (let (($x342 (ite $x301 below0 (ite (= a4 (_ bv7 4)) below1 (ite (= a4 (_ bv8 4)) below2 below3)))))
 (let (($x303 (= a4 (_ bv5 4))))
 (let (($x305 (= a4 (_ bv4 4))))
 (let (($x307 (= a4 (_ bv3 4))))
 (let (($x309 (= a4 (_ bv2 4))))
 (let (($x346 (ite $x309 false (ite $x307 false (ite $x305 false (ite $x303 false $x342))))))
 (let (($x311 (= a4 (_ bv1 4))))
 (let (($x313 (= a4 (_ bv0 4))))
 (let (($x358 (= (ite $x313 false (ite $x311 false $x346)) (ite $x331 false (ite $x329 false $x355)))))
 (=> or4 $x358)))))))))))))))))))))
(assert
 (and (distinct g4 (_ bv0 8)) true))
(assert
 (and (distinct g4 (_ bv255 8)) true))
(assert
 (and (distinct (_ bv71 8) g4) true))
(assert
 (and (distinct (_ bv57 8) g4) true))
(assert
 (and (distinct (_ bv138 8) g4) true))
(assert
 (and (distinct (_ bv140 8) g4) true))
(assert
 (and (distinct (_ bv208 8) g4) true))
(assert
 (and (distinct (_ bv224 8) g4) true))
(assert
 (and (distinct g4 g0) true))
(assert
 (and (distinct g4 g1) true))
(assert
 (and (distinct g4 g2) true))
(assert
 (and (distinct g4 g3) true))
(assert
 (bvult a5 (_ bv11 4)))
(assert
 (bvult b5 (_ bv11 4)))
(assert
 (bvule a5 b5))
(assert
 (let (($x405 (= b5 (_ bv7 4))))
 (let ((?x406 (ite $x405 g1 (ite (= b5 (_ bv8 4)) g2 (ite (= b5 (_ bv9 4)) g3 g4)))))
 (let (($x407 (= b5 (_ bv6 4))))
 (let (($x409 (= b5 (_ bv5 4))))
 (let (($x411 (= b5 (_ bv4 4))))
 (let (($x413 (= b5 (_ bv3 4))))
 (let (($x415 (= b5 (_ bv2 4))))
 (let ((?x416 (ite $x415 (_ bv138 8) (ite $x413 (_ bv140 8) (ite $x411 (_ bv208 8) (ite $x409 (_ bv224 8) (ite $x407 g0 ?x406)))))))
 (let (($x417 (= b5 (_ bv1 4))))
 (let (($x419 (= b5 (_ bv0 4))))
 (let ((?x420 (ite $x419 (_ bv71 8) (ite $x417 (_ bv57 8) ?x416))))
 (let (($x385 (= a5 (_ bv7 4))))
 (let ((?x386 (ite $x385 g1 (ite (= a5 (_ bv8 4)) g2 (ite (= a5 (_ bv9 4)) g3 g4)))))
 (let (($x387 (= a5 (_ bv6 4))))
 (let (($x389 (= a5 (_ bv5 4))))
 (let (($x391 (= a5 (_ bv4 4))))
 (let (($x393 (= a5 (_ bv3 4))))
 (let (($x395 (= a5 (_ bv2 4))))
 (let ((?x396 (ite $x395 (_ bv138 8) (ite $x393 (_ bv140 8) (ite $x391 (_ bv208 8) (ite $x389 (_ bv224 8) (ite $x387 g0 ?x386)))))))
 (let (($x397 (= a5 (_ bv1 4))))
 (let (($x399 (= a5 (_ bv0 4))))
 (let ((?x400 (ite $x399 (_ bv71 8) (ite $x397 (_ bv57 8) ?x396))))
 (= g5 (ite or5 (bvor ?x400 ?x420) (bvand ?x400 ?x420))))))))))))))))))))))))))
(assert
 (= below5 (= (bvand g5 (_ bv200 8)) (_ bv0 8))))
(assert
 (let (($x405 (= b5 (_ bv7 4))))
 (let (($x440 (ite $x405 below1 (ite (= b5 (_ bv8 4)) below2 (ite (= b5 (_ bv9 4)) below3 below4)))))
 (let (($x407 (= b5 (_ bv6 4))))
 (let (($x409 (= b5 (_ bv5 4))))
 (let (($x411 (= b5 (_ bv4 4))))
 (let (($x413 (= b5 (_ bv3 4))))
 (let (($x444 (ite $x413 false (ite $x411 false (ite $x409 false (ite $x407 below0 $x440))))))
 (let (($x415 (= b5 (_ bv2 4))))
 (let (($x417 (= b5 (_ bv1 4))))
 (let (($x419 (= b5 (_ bv0 4))))
 (let (($x385 (= a5 (_ bv7 4))))
 (let (($x430 (ite $x385 below1 (ite (= a5 (_ bv8 4)) below2 (ite (= a5 (_ bv9 4)) below3 below4)))))
 (let (($x387 (= a5 (_ bv6 4))))
 (let (($x389 (= a5 (_ bv5 4))))
 (let (($x391 (= a5 (_ bv4 4))))
 (let (($x393 (= a5 (_ bv3 4))))
 (let (($x434 (ite $x393 false (ite $x391 false (ite $x389 false (ite $x387 below0 $x430))))))
 (let (($x395 (= a5 (_ bv2 4))))
 (let (($x397 (= a5 (_ bv1 4))))
 (let (($x399 (= a5 (_ bv0 4))))
 (let (($x448 (= (ite $x399 false (ite $x397 false (ite $x395 false $x434))) (ite $x419 false (ite $x417 false (ite $x415 false $x444))))))
 (=> or5 $x448)))))))))))))))))))))))
(assert
 (and (distinct g5 (_ bv0 8)) true))
(assert
 (and (distinct g5 (_ bv255 8)) true))
(assert
 (and (distinct (_ bv71 8) g5) true))
(assert
 (and (distinct (_ bv57 8) g5) true))
(assert
 (and (distinct (_ bv138 8) g5) true))
(assert
 (and (distinct (_ bv140 8) g5) true))
(assert
 (and (distinct (_ bv208 8) g5) true))
(assert
 (and (distinct (_ bv224 8) g5) true))
(assert
 (and (distinct g5 g0) true))
(assert
 (and (distinct g5 g1) true))
(assert
 (and (distinct g5 g2) true))
(assert
 (and (distinct g5 g3) true))
(assert
 (and (distinct g5 g4) true))
(assert
 (= (_ bv55 8) g5))
(assert
 (or (and (not or0) (not below0)) (and (not or1) (not below1)) (and (not or2) (not below2)) (and (not or3) (not below3)) (and (not or4) (not below4)) (and (not or5) (not below5))))
(assert
 (or (or (= a1 (_ bv6 4)) (= b1 (_ bv6 4))) (or (= a2 (_ bv6 4)) (= b2 (_ bv6 4))) (or (= a3 (_ bv6 4)) (= b3 (_ bv6 4))) (or (= a4 (_ bv6 4)) (= b4 (_ bv6 4))) (or (= a5 (_ bv6 4)) (= b5 (_ bv6 4)))))
(assert
 (or (or (= a2 (_ bv7 4)) (= b2 (_ bv7 4))) (or (= a3 (_ bv7 4)) (= b3 (_ bv7 4))) (or (= a4 (_ bv7 4)) (= b4 (_ bv7 4))) (or (= a5 (_ bv7 4)) (= b5 (_ bv7 4)))))
(assert
 (or (or (= a3 (_ bv8 4)) (= b3 (_ bv8 4))) (or (= a4 (_ bv8 4)) (= b4 (_ bv8 4))) (or (= a5 (_ bv8 4)) (= b5 (_ bv8 4)))))
(assert
 (or (or (= a4 (_ bv9 4)) (= b4 (_ bv9 4))) (or (= a5 (_ bv9 4)) (= b5 (_ bv9 4)))))
(assert
 (or (or (= a5 (_ bv10 4)) (= b5 (_ bv10 4)))))
(assert
 (let ((?x516 (concat (concat (ite or1 (_ bv0 1) (_ bv1 1)) a1) b1)))
 (let (($x485 (= b1 (_ bv6 4))))
 (let (($x484 (= a1 (_ bv6 4))))
 (or $x484 $x485 (bvule (concat (concat (ite or0 (_ bv0 1) (_ bv1 1)) a0) b0) ?x516))))))
(assert
 (let ((?x524 (concat (concat (ite or2 (_ bv0 1) (_ bv1 1)) a2) b2)))
 (let ((?x516 (concat (concat (ite or1 (_ bv0 1) (_ bv1 1)) a1) b1)))
 (let (($x493 (= b2 (_ bv7 4))))
 (let (($x492 (= a2 (_ bv7 4))))
 (or $x492 $x493 (bvule ?x516 ?x524)))))))
(assert
 (let ((?x529 (concat (concat (ite or3 (_ bv0 1) (_ bv1 1)) a3) b3)))
 (let ((?x524 (concat (concat (ite or2 (_ bv0 1) (_ bv1 1)) a2) b2)))
 (let (($x500 (= b3 (_ bv8 4))))
 (let (($x499 (= a3 (_ bv8 4))))
 (or $x499 $x500 (bvule ?x524 ?x529)))))))
(assert
 (let ((?x534 (concat (concat (ite or4 (_ bv0 1) (_ bv1 1)) a4) b4)))
 (let ((?x529 (concat (concat (ite or3 (_ bv0 1) (_ bv1 1)) a3) b3)))
 (let (($x506 (= b4 (_ bv9 4))))
 (let (($x505 (= a4 (_ bv9 4))))
 (or $x505 $x506 (bvule ?x529 ?x534)))))))
(assert
 (let ((?x539 (concat (concat (ite or5 (_ bv0 1) (_ bv1 1)) a5) b5)))
(let ((?x534 (concat (concat (ite or4 (_ bv0 1) (_ bv1 1)) a4) b4)))
(let (($x511 (= b5 (_ bv10 4))))
(let (($x510 (= a5 (_ bv10 4))))
(or $x510 $x511 (bvule ?x534 ?x539)))))))
(check-sat)
