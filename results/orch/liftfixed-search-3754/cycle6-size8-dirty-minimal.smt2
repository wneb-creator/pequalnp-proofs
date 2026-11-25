; benchmark generated from python API
(set-info :status unknown)
(declare-fun a0 () (_ BitVec 4))
(declare-fun b0 () (_ BitVec 4))
(declare-fun or0 () Bool)
(declare-fun g0 () (_ BitVec 11))
(declare-fun below0 () Bool)
(declare-fun a1 () (_ BitVec 4))
(declare-fun b1 () (_ BitVec 4))
(declare-fun or1 () Bool)
(declare-fun g1 () (_ BitVec 11))
(declare-fun below1 () Bool)
(declare-fun a2 () (_ BitVec 4))
(declare-fun b2 () (_ BitVec 4))
(declare-fun or2 () Bool)
(declare-fun g2 () (_ BitVec 11))
(declare-fun below2 () Bool)
(declare-fun a3 () (_ BitVec 4))
(declare-fun b3 () (_ BitVec 4))
(declare-fun or3 () Bool)
(declare-fun g3 () (_ BitVec 11))
(declare-fun below3 () Bool)
(declare-fun a4 () (_ BitVec 4))
(declare-fun b4 () (_ BitVec 4))
(declare-fun or4 () Bool)
(declare-fun g4 () (_ BitVec 11))
(declare-fun below4 () Bool)
(declare-fun a5 () (_ BitVec 4))
(declare-fun b5 () (_ BitVec 4))
(declare-fun or5 () Bool)
(declare-fun g5 () (_ BitVec 11))
(declare-fun below5 () Bool)
(declare-fun a6 () (_ BitVec 4))
(declare-fun b6 () (_ BitVec 4))
(declare-fun or6 () Bool)
(declare-fun g6 () (_ BitVec 11))
(declare-fun below6 () Bool)
(declare-fun a7 () (_ BitVec 4))
(declare-fun b7 () (_ BitVec 4))
(declare-fun or7 () Bool)
(declare-fun g7 () (_ BitVec 11))
(declare-fun below7 () Bool)
(assert
 (bvult a0 (_ bv6 4)))
(assert
 (bvult b0 (_ bv6 4)))
(assert
 (bvule a0 b0))
(assert
 (let (($x41 (= b0 (_ bv2 4))))
 (let ((?x42 (ite $x41 (_ bv298 11) (ite (= b0 (_ bv3 4)) (_ bv588 11) (ite (= b0 (_ bv4 4)) (_ bv1136 11) (_ bv1920 11))))))
 (let (($x43 (= b0 (_ bv1 4))))
 (let (($x45 (= b0 (_ bv0 4))))
 (let ((?x46 (ite $x45 (_ bv165 11) (ite $x43 (_ bv531 11) ?x42))))
 (let (($x29 (= a0 (_ bv2 4))))
 (let ((?x30 (ite $x29 (_ bv298 11) (ite (= a0 (_ bv3 4)) (_ bv588 11) (ite (= a0 (_ bv4 4)) (_ bv1136 11) (_ bv1920 11))))))
 (let (($x32 (= a0 (_ bv1 4))))
 (let (($x35 (= a0 (_ bv0 4))))
 (let ((?x36 (ite $x35 (_ bv165 11) (ite $x32 (_ bv531 11) ?x30))))
 (= g0 (ite or0 (bvor ?x36 ?x46) (bvand ?x36 ?x46))))))))))))))
(assert
 (= below0 (= (bvand g0 (_ bv820 11)) (_ bv0 11))))
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
 (and (distinct g0 (_ bv0 11)) true))
(assert
 (and (distinct g0 (_ bv2047 11)) true))
(assert
 (and (distinct (_ bv165 11) g0) true))
(assert
 (and (distinct (_ bv531 11) g0) true))
(assert
 (and (distinct (_ bv298 11) g0) true))
(assert
 (and (distinct (_ bv588 11) g0) true))
(assert
 (and (distinct (_ bv1136 11) g0) true))
(assert
 (and (distinct (_ bv1920 11) g0) true))
(assert
 (bvult a1 (_ bv7 4)))
(assert
 (bvult b1 (_ bv7 4)))
(assert
 (bvule a1 b1))
(assert
 (let (($x103 (= b1 (_ bv3 4))))
 (let ((?x104 (ite $x103 (_ bv588 11) (ite (= b1 (_ bv4 4)) (_ bv1136 11) (ite (= b1 (_ bv5 4)) (_ bv1920 11) g0)))))
 (let (($x105 (= b1 (_ bv2 4))))
 (let (($x107 (= b1 (_ bv1 4))))
 (let (($x109 (= b1 (_ bv0 4))))
 (let ((?x110 (ite $x109 (_ bv165 11) (ite $x107 (_ bv531 11) (ite $x105 (_ bv298 11) ?x104)))))
 (let (($x91 (= a1 (_ bv3 4))))
 (let ((?x92 (ite $x91 (_ bv588 11) (ite (= a1 (_ bv4 4)) (_ bv1136 11) (ite (= a1 (_ bv5 4)) (_ bv1920 11) g0)))))
 (let (($x93 (= a1 (_ bv2 4))))
 (let (($x95 (= a1 (_ bv1 4))))
 (let (($x97 (= a1 (_ bv0 4))))
 (let ((?x98 (ite $x97 (_ bv165 11) (ite $x95 (_ bv531 11) (ite $x93 (_ bv298 11) ?x92)))))
 (= g1 (ite or1 (bvor ?x98 ?x110) (bvand ?x98 ?x110))))))))))))))))
(assert
 (= below1 (= (bvand g1 (_ bv820 11)) (_ bv0 11))))
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
 (and (distinct g1 (_ bv0 11)) true))
(assert
 (and (distinct g1 (_ bv2047 11)) true))
(assert
 (and (distinct (_ bv165 11) g1) true))
(assert
 (and (distinct (_ bv531 11) g1) true))
(assert
 (and (distinct (_ bv298 11) g1) true))
(assert
 (and (distinct (_ bv588 11) g1) true))
(assert
 (and (distinct (_ bv1136 11) g1) true))
(assert
 (and (distinct (_ bv1920 11) g1) true))
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
 (let ((?x169 (ite $x168 (_ bv1136 11) (ite (= b2 (_ bv5 4)) (_ bv1920 11) (ite (= b2 (_ bv6 4)) g0 g1)))))
 (let (($x170 (= b2 (_ bv3 4))))
 (let (($x172 (= b2 (_ bv2 4))))
 (let (($x174 (= b2 (_ bv1 4))))
 (let (($x176 (= b2 (_ bv0 4))))
 (let ((?x177 (ite $x176 (_ bv165 11) (ite $x174 (_ bv531 11) (ite $x172 (_ bv298 11) (ite $x170 (_ bv588 11) ?x169))))))
 (let (($x154 (= a2 (_ bv4 4))))
 (let ((?x155 (ite $x154 (_ bv1136 11) (ite (= a2 (_ bv5 4)) (_ bv1920 11) (ite (= a2 (_ bv6 4)) g0 g1)))))
 (let (($x156 (= a2 (_ bv3 4))))
 (let (($x158 (= a2 (_ bv2 4))))
 (let (($x160 (= a2 (_ bv1 4))))
 (let (($x162 (= a2 (_ bv0 4))))
 (let ((?x163 (ite $x162 (_ bv165 11) (ite $x160 (_ bv531 11) (ite $x158 (_ bv298 11) (ite $x156 (_ bv588 11) ?x155))))))
 (= g2 (ite or2 (bvor ?x163 ?x177) (bvand ?x163 ?x177))))))))))))))))))
(assert
 (= below2 (= (bvand g2 (_ bv820 11)) (_ bv0 11))))
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
 (and (distinct g2 (_ bv0 11)) true))
(assert
 (and (distinct g2 (_ bv2047 11)) true))
(assert
 (and (distinct (_ bv165 11) g2) true))
(assert
 (and (distinct (_ bv531 11) g2) true))
(assert
 (and (distinct (_ bv298 11) g2) true))
(assert
 (and (distinct (_ bv588 11) g2) true))
(assert
 (and (distinct (_ bv1136 11) g2) true))
(assert
 (and (distinct (_ bv1920 11) g2) true))
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
 (let ((?x241 (ite $x240 (_ bv1920 11) (ite (= b3 (_ bv6 4)) g0 (ite (= b3 (_ bv7 4)) g1 g2)))))
 (let (($x242 (= b3 (_ bv4 4))))
 (let (($x244 (= b3 (_ bv3 4))))
 (let (($x246 (= b3 (_ bv2 4))))
 (let (($x248 (= b3 (_ bv1 4))))
 (let (($x250 (= b3 (_ bv0 4))))
 (let ((?x251 (ite $x250 (_ bv165 11) (ite $x248 (_ bv531 11) (ite $x246 (_ bv298 11) (ite $x244 (_ bv588 11) (ite $x242 (_ bv1136 11) ?x241)))))))
 (let (($x224 (= a3 (_ bv5 4))))
 (let ((?x225 (ite $x224 (_ bv1920 11) (ite (= a3 (_ bv6 4)) g0 (ite (= a3 (_ bv7 4)) g1 g2)))))
 (let (($x226 (= a3 (_ bv4 4))))
 (let (($x228 (= a3 (_ bv3 4))))
 (let (($x230 (= a3 (_ bv2 4))))
 (let (($x232 (= a3 (_ bv1 4))))
 (let (($x234 (= a3 (_ bv0 4))))
 (let ((?x235 (ite $x234 (_ bv165 11) (ite $x232 (_ bv531 11) (ite $x230 (_ bv298 11) (ite $x228 (_ bv588 11) (ite $x226 (_ bv1136 11) ?x225)))))))
 (= g3 (ite or3 (bvor ?x235 ?x251) (bvand ?x235 ?x251))))))))))))))))))))
(assert
 (= below3 (= (bvand g3 (_ bv820 11)) (_ bv0 11))))
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
 (and (distinct g3 (_ bv0 11)) true))
(assert
 (and (distinct g3 (_ bv2047 11)) true))
(assert
 (and (distinct (_ bv165 11) g3) true))
(assert
 (and (distinct (_ bv531 11) g3) true))
(assert
 (and (distinct (_ bv298 11) g3) true))
(assert
 (and (distinct (_ bv588 11) g3) true))
(assert
 (and (distinct (_ bv1136 11) g3) true))
(assert
 (and (distinct (_ bv1920 11) g3) true))
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
 (let ((?x330 (ite $x329 (_ bv531 11) (ite $x327 (_ bv298 11) (ite $x325 (_ bv588 11) (ite $x323 (_ bv1136 11) (ite $x321 (_ bv1920 11) ?x320)))))))
 (let (($x331 (= b4 (_ bv0 4))))
 (let ((?x332 (ite $x331 (_ bv165 11) ?x330)))
 (let (($x301 (= a4 (_ bv6 4))))
 (let ((?x302 (ite $x301 g0 (ite (= a4 (_ bv7 4)) g1 (ite (= a4 (_ bv8 4)) g2 g3)))))
 (let (($x303 (= a4 (_ bv5 4))))
 (let (($x305 (= a4 (_ bv4 4))))
 (let (($x307 (= a4 (_ bv3 4))))
 (let (($x309 (= a4 (_ bv2 4))))
 (let (($x311 (= a4 (_ bv1 4))))
 (let ((?x312 (ite $x311 (_ bv531 11) (ite $x309 (_ bv298 11) (ite $x307 (_ bv588 11) (ite $x305 (_ bv1136 11) (ite $x303 (_ bv1920 11) ?x302)))))))
 (let (($x313 (= a4 (_ bv0 4))))
 (let ((?x314 (ite $x313 (_ bv165 11) ?x312)))
 (= g4 (ite or4 (bvor ?x314 ?x332) (bvand ?x314 ?x332))))))))))))))))))))))))
(assert
 (= below4 (= (bvand g4 (_ bv820 11)) (_ bv0 11))))
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
 (and (distinct g4 (_ bv0 11)) true))
(assert
 (and (distinct g4 (_ bv2047 11)) true))
(assert
 (and (distinct (_ bv165 11) g4) true))
(assert
 (and (distinct (_ bv531 11) g4) true))
(assert
 (and (distinct (_ bv298 11) g4) true))
(assert
 (and (distinct (_ bv588 11) g4) true))
(assert
 (and (distinct (_ bv1136 11) g4) true))
(assert
 (and (distinct (_ bv1920 11) g4) true))
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
 (let ((?x416 (ite $x415 (_ bv298 11) (ite $x413 (_ bv588 11) (ite $x411 (_ bv1136 11) (ite $x409 (_ bv1920 11) (ite $x407 g0 ?x406)))))))
 (let (($x417 (= b5 (_ bv1 4))))
 (let (($x419 (= b5 (_ bv0 4))))
 (let ((?x420 (ite $x419 (_ bv165 11) (ite $x417 (_ bv531 11) ?x416))))
 (let (($x385 (= a5 (_ bv7 4))))
 (let ((?x386 (ite $x385 g1 (ite (= a5 (_ bv8 4)) g2 (ite (= a5 (_ bv9 4)) g3 g4)))))
 (let (($x387 (= a5 (_ bv6 4))))
 (let (($x389 (= a5 (_ bv5 4))))
 (let (($x391 (= a5 (_ bv4 4))))
 (let (($x393 (= a5 (_ bv3 4))))
 (let (($x395 (= a5 (_ bv2 4))))
 (let ((?x396 (ite $x395 (_ bv298 11) (ite $x393 (_ bv588 11) (ite $x391 (_ bv1136 11) (ite $x389 (_ bv1920 11) (ite $x387 g0 ?x386)))))))
 (let (($x397 (= a5 (_ bv1 4))))
 (let (($x399 (= a5 (_ bv0 4))))
 (let ((?x400 (ite $x399 (_ bv165 11) (ite $x397 (_ bv531 11) ?x396))))
 (= g5 (ite or5 (bvor ?x400 ?x420) (bvand ?x400 ?x420))))))))))))))))))))))))))
(assert
 (= below5 (= (bvand g5 (_ bv820 11)) (_ bv0 11))))
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
 (and (distinct g5 (_ bv0 11)) true))
(assert
 (and (distinct g5 (_ bv2047 11)) true))
(assert
 (and (distinct (_ bv165 11) g5) true))
(assert
 (and (distinct (_ bv531 11) g5) true))
(assert
 (and (distinct (_ bv298 11) g5) true))
(assert
 (and (distinct (_ bv588 11) g5) true))
(assert
 (and (distinct (_ bv1136 11) g5) true))
(assert
 (and (distinct (_ bv1920 11) g5) true))
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
 (bvult a6 (_ bv12 4)))
(assert
 (bvult b6 (_ bv12 4)))
(assert
 (bvule a6 b6))
(assert
 (let (($x498 (= b6 (_ bv8 4))))
 (let ((?x499 (ite $x498 g2 (ite (= b6 (_ bv9 4)) g3 (ite (= b6 (_ bv10 4)) g4 g5)))))
 (let (($x500 (= b6 (_ bv7 4))))
 (let (($x502 (= b6 (_ bv6 4))))
 (let (($x504 (= b6 (_ bv5 4))))
 (let (($x506 (= b6 (_ bv4 4))))
 (let (($x508 (= b6 (_ bv3 4))))
 (let ((?x509 (ite $x508 (_ bv588 11) (ite $x506 (_ bv1136 11) (ite $x504 (_ bv1920 11) (ite $x502 g0 (ite $x500 g1 ?x499)))))))
 (let (($x510 (= b6 (_ bv2 4))))
 (let (($x512 (= b6 (_ bv1 4))))
 (let (($x514 (= b6 (_ bv0 4))))
 (let ((?x515 (ite $x514 (_ bv165 11) (ite $x512 (_ bv531 11) (ite $x510 (_ bv298 11) ?x509)))))
 (let (($x476 (= a6 (_ bv8 4))))
 (let ((?x477 (ite $x476 g2 (ite (= a6 (_ bv9 4)) g3 (ite (= a6 (_ bv10 4)) g4 g5)))))
 (let (($x478 (= a6 (_ bv7 4))))
 (let (($x480 (= a6 (_ bv6 4))))
 (let (($x482 (= a6 (_ bv5 4))))
 (let (($x484 (= a6 (_ bv4 4))))
 (let (($x486 (= a6 (_ bv3 4))))
 (let ((?x487 (ite $x486 (_ bv588 11) (ite $x484 (_ bv1136 11) (ite $x482 (_ bv1920 11) (ite $x480 g0 (ite $x478 g1 ?x477)))))))
 (let (($x488 (= a6 (_ bv2 4))))
 (let (($x490 (= a6 (_ bv1 4))))
 (let (($x492 (= a6 (_ bv0 4))))
 (let ((?x493 (ite $x492 (_ bv165 11) (ite $x490 (_ bv531 11) (ite $x488 (_ bv298 11) ?x487)))))
 (= g6 (ite or6 (bvor ?x493 ?x515) (bvand ?x493 ?x515))))))))))))))))))))))))))))
(assert
 (= below6 (= (bvand g6 (_ bv820 11)) (_ bv0 11))))
(assert
 (let (($x498 (= b6 (_ bv8 4))))
 (let (($x536 (ite $x498 below2 (ite (= b6 (_ bv9 4)) below3 (ite (= b6 (_ bv10 4)) below4 below5)))))
 (let (($x500 (= b6 (_ bv7 4))))
 (let (($x502 (= b6 (_ bv6 4))))
 (let (($x504 (= b6 (_ bv5 4))))
 (let (($x506 (= b6 (_ bv4 4))))
 (let (($x540 (ite $x506 false (ite $x504 false (ite $x502 below0 (ite $x500 below1 $x536))))))
 (let (($x508 (= b6 (_ bv3 4))))
 (let (($x510 (= b6 (_ bv2 4))))
 (let (($x512 (= b6 (_ bv1 4))))
 (let (($x514 (= b6 (_ bv0 4))))
 (let (($x544 (ite $x514 false (ite $x512 false (ite $x510 false (ite $x508 false $x540))))))
 (let (($x476 (= a6 (_ bv8 4))))
 (let (($x525 (ite $x476 below2 (ite (= a6 (_ bv9 4)) below3 (ite (= a6 (_ bv10 4)) below4 below5)))))
 (let (($x478 (= a6 (_ bv7 4))))
 (let (($x480 (= a6 (_ bv6 4))))
 (let (($x482 (= a6 (_ bv5 4))))
 (let (($x484 (= a6 (_ bv4 4))))
 (let (($x529 (ite $x484 false (ite $x482 false (ite $x480 below0 (ite $x478 below1 $x525))))))
 (let (($x486 (= a6 (_ bv3 4))))
 (let (($x488 (= a6 (_ bv2 4))))
 (let (($x490 (= a6 (_ bv1 4))))
 (let (($x492 (= a6 (_ bv0 4))))
 (let (($x533 (ite $x492 false (ite $x490 false (ite $x488 false (ite $x486 false $x529))))))
 (=> or6 (= $x533 $x544)))))))))))))))))))))))))))
(assert
 (and (distinct g6 (_ bv0 11)) true))
(assert
 (and (distinct g6 (_ bv2047 11)) true))
(assert
 (and (distinct (_ bv165 11) g6) true))
(assert
 (and (distinct (_ bv531 11) g6) true))
(assert
 (and (distinct (_ bv298 11) g6) true))
(assert
 (and (distinct (_ bv588 11) g6) true))
(assert
 (and (distinct (_ bv1136 11) g6) true))
(assert
 (and (distinct (_ bv1920 11) g6) true))
(assert
 (and (distinct g6 g0) true))
(assert
 (and (distinct g6 g1) true))
(assert
 (and (distinct g6 g2) true))
(assert
 (and (distinct g6 g3) true))
(assert
 (and (distinct g6 g4) true))
(assert
 (and (distinct g6 g5) true))
(assert
 (bvult a7 (_ bv13 4)))
(assert
 (bvult b7 (_ bv13 4)))
(assert
 (bvule a7 b7))
(assert
 (let (($x598 (= b7 (_ bv9 4))))
 (let ((?x599 (ite $x598 g3 (ite (= b7 (_ bv10 4)) g4 (ite (= b7 (_ bv11 4)) g5 g6)))))
 (let (($x600 (= b7 (_ bv8 4))))
 (let (($x602 (= b7 (_ bv7 4))))
 (let (($x604 (= b7 (_ bv6 4))))
 (let (($x606 (= b7 (_ bv5 4))))
 (let (($x608 (= b7 (_ bv4 4))))
 (let ((?x609 (ite $x608 (_ bv1136 11) (ite $x606 (_ bv1920 11) (ite $x604 g0 (ite $x602 g1 (ite $x600 g2 ?x599)))))))
 (let (($x610 (= b7 (_ bv3 4))))
 (let (($x612 (= b7 (_ bv2 4))))
 (let (($x614 (= b7 (_ bv1 4))))
 (let (($x616 (= b7 (_ bv0 4))))
 (let ((?x617 (ite $x616 (_ bv165 11) (ite $x614 (_ bv531 11) (ite $x612 (_ bv298 11) (ite $x610 (_ bv588 11) ?x609))))))
 (let (($x574 (= a7 (_ bv9 4))))
 (let ((?x575 (ite $x574 g3 (ite (= a7 (_ bv10 4)) g4 (ite (= a7 (_ bv11 4)) g5 g6)))))
 (let (($x576 (= a7 (_ bv8 4))))
 (let (($x578 (= a7 (_ bv7 4))))
 (let (($x580 (= a7 (_ bv6 4))))
 (let (($x582 (= a7 (_ bv5 4))))
 (let (($x584 (= a7 (_ bv4 4))))
 (let ((?x585 (ite $x584 (_ bv1136 11) (ite $x582 (_ bv1920 11) (ite $x580 g0 (ite $x578 g1 (ite $x576 g2 ?x575)))))))
 (let (($x586 (= a7 (_ bv3 4))))
 (let (($x588 (= a7 (_ bv2 4))))
 (let (($x590 (= a7 (_ bv1 4))))
 (let (($x592 (= a7 (_ bv0 4))))
 (let ((?x593 (ite $x592 (_ bv165 11) (ite $x590 (_ bv531 11) (ite $x588 (_ bv298 11) (ite $x586 (_ bv588 11) ?x585))))))
 (= g7 (ite or7 (bvor ?x593 ?x617) (bvand ?x593 ?x617))))))))))))))))))))))))))))))
(assert
 (= below7 (= (bvand g7 (_ bv820 11)) (_ bv0 11))))
(assert
 (let (($x598 (= b7 (_ bv9 4))))
 (let (($x639 (ite $x598 below3 (ite (= b7 (_ bv10 4)) below4 (ite (= b7 (_ bv11 4)) below5 below6)))))
 (let (($x600 (= b7 (_ bv8 4))))
 (let (($x602 (= b7 (_ bv7 4))))
 (let (($x604 (= b7 (_ bv6 4))))
 (let (($x606 (= b7 (_ bv5 4))))
 (let (($x643 (ite $x606 false (ite $x604 below0 (ite $x602 below1 (ite $x600 below2 $x639))))))
 (let (($x608 (= b7 (_ bv4 4))))
 (let (($x610 (= b7 (_ bv3 4))))
 (let (($x612 (= b7 (_ bv2 4))))
 (let (($x614 (= b7 (_ bv1 4))))
 (let (($x647 (ite $x614 false (ite $x612 false (ite $x610 false (ite $x608 false $x643))))))
 (let (($x616 (= b7 (_ bv0 4))))
 (let (($x574 (= a7 (_ bv9 4))))
 (let (($x627 (ite $x574 below3 (ite (= a7 (_ bv10 4)) below4 (ite (= a7 (_ bv11 4)) below5 below6)))))
 (let (($x576 (= a7 (_ bv8 4))))
 (let (($x578 (= a7 (_ bv7 4))))
 (let (($x580 (= a7 (_ bv6 4))))
 (let (($x582 (= a7 (_ bv5 4))))
 (let (($x631 (ite $x582 false (ite $x580 below0 (ite $x578 below1 (ite $x576 below2 $x627))))))
 (let (($x584 (= a7 (_ bv4 4))))
 (let (($x586 (= a7 (_ bv3 4))))
 (let (($x588 (= a7 (_ bv2 4))))
 (let (($x590 (= a7 (_ bv1 4))))
 (let (($x635 (ite $x590 false (ite $x588 false (ite $x586 false (ite $x584 false $x631))))))
 (let (($x592 (= a7 (_ bv0 4))))
 (=> or7 (= (ite $x592 false $x635) (ite $x616 false $x647))))))))))))))))))))))))))))))
(assert
 (and (distinct g7 (_ bv0 11)) true))
(assert
 (and (distinct g7 (_ bv2047 11)) true))
(assert
 (and (distinct (_ bv165 11) g7) true))
(assert
 (and (distinct (_ bv531 11) g7) true))
(assert
 (and (distinct (_ bv298 11) g7) true))
(assert
 (and (distinct (_ bv588 11) g7) true))
(assert
 (and (distinct (_ bv1136 11) g7) true))
(assert
 (and (distinct (_ bv1920 11) g7) true))
(assert
 (and (distinct g7 g0) true))
(assert
 (and (distinct g7 g1) true))
(assert
 (and (distinct g7 g2) true))
(assert
 (and (distinct g7 g3) true))
(assert
 (and (distinct g7 g4) true))
(assert
 (and (distinct g7 g5) true))
(assert
 (and (distinct g7 g6) true))
(assert
 (= (_ bv1227 11) g7))
(assert
 (or (and (not or0) (not below0)) (and (not or1) (not below1)) (and (not or2) (not below2)) (and (not or3) (not below3)) (and (not or4) (not below4)) (and (not or5) (not below5)) (and (not or6) (not below6)) (and (not or7) (not below7))))
(assert
 (or (or (= a1 (_ bv6 4)) (= b1 (_ bv6 4))) (or (= a2 (_ bv6 4)) (= b2 (_ bv6 4))) (or (= a3 (_ bv6 4)) (= b3 (_ bv6 4))) (or (= a4 (_ bv6 4)) (= b4 (_ bv6 4))) (or (= a5 (_ bv6 4)) (= b5 (_ bv6 4))) (or (= a6 (_ bv6 4)) (= b6 (_ bv6 4))) (or (= a7 (_ bv6 4)) (= b7 (_ bv6 4)))))
(assert
 (or (or (= a2 (_ bv7 4)) (= b2 (_ bv7 4))) (or (= a3 (_ bv7 4)) (= b3 (_ bv7 4))) (or (= a4 (_ bv7 4)) (= b4 (_ bv7 4))) (or (= a5 (_ bv7 4)) (= b5 (_ bv7 4))) (or (= a6 (_ bv7 4)) (= b6 (_ bv7 4))) (or (= a7 (_ bv7 4)) (= b7 (_ bv7 4)))))
(assert
 (or (or (= a3 (_ bv8 4)) (= b3 (_ bv8 4))) (or (= a4 (_ bv8 4)) (= b4 (_ bv8 4))) (or (= a5 (_ bv8 4)) (= b5 (_ bv8 4))) (or (= a6 (_ bv8 4)) (= b6 (_ bv8 4))) (or (= a7 (_ bv8 4)) (= b7 (_ bv8 4)))))
(assert
 (or (or (= a4 (_ bv9 4)) (= b4 (_ bv9 4))) (or (= a5 (_ bv9 4)) (= b5 (_ bv9 4))) (or (= a6 (_ bv9 4)) (= b6 (_ bv9 4))) (or (= a7 (_ bv9 4)) (= b7 (_ bv9 4)))))
(assert
 (or (or (= a5 (_ bv10 4)) (= b5 (_ bv10 4))) (or (= a6 (_ bv10 4)) (= b6 (_ bv10 4))) (or (= a7 (_ bv10 4)) (= b7 (_ bv10 4)))))
(assert
 (or (or (= a6 (_ bv11 4)) (= b6 (_ bv11 4))) (or (= a7 (_ bv11 4)) (= b7 (_ bv11 4)))))
(assert
 (or (or (= a7 (_ bv12 4)) (= b7 (_ bv12 4)))))
(assert
 (let ((?x744 (concat (concat (ite or1 (_ bv0 1) (_ bv1 1)) a1) b1)))
 (let (($x694 (= b1 (_ bv6 4))))
 (let (($x693 (= a1 (_ bv6 4))))
 (or $x693 $x694 (bvule (concat (concat (ite or0 (_ bv0 1) (_ bv1 1)) a0) b0) ?x744))))))
(assert
 (let ((?x752 (concat (concat (ite or2 (_ bv0 1) (_ bv1 1)) a2) b2)))
 (let ((?x744 (concat (concat (ite or1 (_ bv0 1) (_ bv1 1)) a1) b1)))
 (let (($x704 (= b2 (_ bv7 4))))
 (let (($x703 (= a2 (_ bv7 4))))
 (or $x703 $x704 (bvule ?x744 ?x752)))))))
(assert
 (let ((?x757 (concat (concat (ite or3 (_ bv0 1) (_ bv1 1)) a3) b3)))
 (let ((?x752 (concat (concat (ite or2 (_ bv0 1) (_ bv1 1)) a2) b2)))
 (let (($x713 (= b3 (_ bv8 4))))
 (let (($x712 (= a3 (_ bv8 4))))
 (or $x712 $x713 (bvule ?x752 ?x757)))))))
(assert
 (let ((?x762 (concat (concat (ite or4 (_ bv0 1) (_ bv1 1)) a4) b4)))
 (let ((?x757 (concat (concat (ite or3 (_ bv0 1) (_ bv1 1)) a3) b3)))
 (let (($x721 (= b4 (_ bv9 4))))
 (let (($x720 (= a4 (_ bv9 4))))
 (or $x720 $x721 (bvule ?x757 ?x762)))))))
(assert
 (let ((?x767 (concat (concat (ite or5 (_ bv0 1) (_ bv1 1)) a5) b5)))
 (let ((?x762 (concat (concat (ite or4 (_ bv0 1) (_ bv1 1)) a4) b4)))
 (let (($x728 (= b5 (_ bv10 4))))
 (let (($x727 (= a5 (_ bv10 4))))
 (or $x727 $x728 (bvule ?x762 ?x767)))))))
(assert
 (let ((?x772 (concat (concat (ite or6 (_ bv0 1) (_ bv1 1)) a6) b6)))
 (let ((?x767 (concat (concat (ite or5 (_ bv0 1) (_ bv1 1)) a5) b5)))
 (let (($x734 (= b6 (_ bv11 4))))
 (let (($x733 (= a6 (_ bv11 4))))
 (or $x733 $x734 (bvule ?x767 ?x772)))))))
(assert
 (let ((?x777 (concat (concat (ite or7 (_ bv0 1) (_ bv1 1)) a7) b7)))
(let ((?x772 (concat (concat (ite or6 (_ bv0 1) (_ bv1 1)) a6) b6)))
(let (($x739 (= b7 (_ bv12 4))))
(let (($x738 (= a7 (_ bv12 4))))
(or $x738 $x739 (bvule ?x772 ?x777)))))))
(check-sat)
