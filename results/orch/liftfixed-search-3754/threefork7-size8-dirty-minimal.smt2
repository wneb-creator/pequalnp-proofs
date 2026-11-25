; benchmark generated from python API
(set-info :status unknown)
(declare-fun a0 () (_ BitVec 4))
(declare-fun b0 () (_ BitVec 4))
(declare-fun or0 () Bool)
(declare-fun g0 () (_ BitVec 14))
(declare-fun below0 () Bool)
(declare-fun a1 () (_ BitVec 4))
(declare-fun b1 () (_ BitVec 4))
(declare-fun or1 () Bool)
(declare-fun g1 () (_ BitVec 14))
(declare-fun below1 () Bool)
(declare-fun a2 () (_ BitVec 4))
(declare-fun b2 () (_ BitVec 4))
(declare-fun or2 () Bool)
(declare-fun g2 () (_ BitVec 14))
(declare-fun below2 () Bool)
(declare-fun a3 () (_ BitVec 4))
(declare-fun b3 () (_ BitVec 4))
(declare-fun or3 () Bool)
(declare-fun g3 () (_ BitVec 14))
(declare-fun below3 () Bool)
(declare-fun a4 () (_ BitVec 4))
(declare-fun b4 () (_ BitVec 4))
(declare-fun or4 () Bool)
(declare-fun g4 () (_ BitVec 14))
(declare-fun below4 () Bool)
(declare-fun a5 () (_ BitVec 4))
(declare-fun b5 () (_ BitVec 4))
(declare-fun or5 () Bool)
(declare-fun g5 () (_ BitVec 14))
(declare-fun below5 () Bool)
(declare-fun a6 () (_ BitVec 4))
(declare-fun b6 () (_ BitVec 4))
(declare-fun or6 () Bool)
(declare-fun g6 () (_ BitVec 14))
(declare-fun below6 () Bool)
(declare-fun a7 () (_ BitVec 4))
(declare-fun b7 () (_ BitVec 4))
(declare-fun or7 () Bool)
(declare-fun g7 () (_ BitVec 14))
(declare-fun below7 () Bool)
(assert
 (bvult a0 (_ bv7 4)))
(assert
 (bvult b0 (_ bv7 4)))
(assert
 (bvule a0 b0))
(assert
 (let (($x45 (= b0 (_ bv3 4))))
 (let ((?x46 (ite $x45 (_ bv1644 14) (ite (= b0 (_ bv4 4)) (_ bv6536 14) (ite (= b0 (_ bv5 4)) (_ bv8688 14) (_ bv15872 14))))))
 (let (($x47 (= b0 (_ bv2 4))))
 (let (($x49 (= b0 (_ bv1 4))))
 (let (($x51 (= b0 (_ bv0 4))))
 (let ((?x52 (ite $x51 (_ bv4117 14) (ite $x49 (_ bv2723 14) (ite $x47 (_ bv5442 14) ?x46)))))
 (let (($x30 (= a0 (_ bv3 4))))
 (let ((?x31 (ite $x30 (_ bv1644 14) (ite (= a0 (_ bv4 4)) (_ bv6536 14) (ite (= a0 (_ bv5 4)) (_ bv8688 14) (_ bv15872 14))))))
 (let (($x33 (= a0 (_ bv2 4))))
 (let (($x36 (= a0 (_ bv1 4))))
 (let (($x39 (= a0 (_ bv0 4))))
 (let ((?x40 (ite $x39 (_ bv4117 14) (ite $x36 (_ bv2723 14) (ite $x33 (_ bv5442 14) ?x31)))))
 (= g0 (ite or0 (bvor ?x40 ?x52) (bvand ?x40 ?x52))))))))))))))))
(assert
 (= below0 (= (bvand g0 (_ bv8160 14)) (_ bv0 14))))
(assert
 (let (($x45 (= b0 (_ bv3 4))))
 (let (($x70 (ite $x45 false (ite (= b0 (_ bv4 4)) false (ite (= b0 (_ bv5 4)) false false)))))
 (let (($x47 (= b0 (_ bv2 4))))
 (let (($x49 (= b0 (_ bv1 4))))
 (let (($x51 (= b0 (_ bv0 4))))
 (let (($x30 (= a0 (_ bv3 4))))
 (let (($x64 (ite $x30 false (ite (= a0 (_ bv4 4)) false (ite (= a0 (_ bv5 4)) false false)))))
 (let (($x33 (= a0 (_ bv2 4))))
 (let (($x36 (= a0 (_ bv1 4))))
 (let (($x39 (= a0 (_ bv0 4))))
 (let (($x74 (= (ite $x39 false (ite $x36 false (ite $x33 false $x64))) (ite $x51 false (ite $x49 false (ite $x47 false $x70))))))
 (=> or0 $x74)))))))))))))
(assert
 (and (distinct g0 (_ bv0 14)) true))
(assert
 (and (distinct g0 (_ bv16383 14)) true))
(assert
 (and (distinct (_ bv4117 14) g0) true))
(assert
 (and (distinct (_ bv2723 14) g0) true))
(assert
 (and (distinct (_ bv5442 14) g0) true))
(assert
 (and (distinct (_ bv1644 14) g0) true))
(assert
 (and (distinct (_ bv6536 14) g0) true))
(assert
 (and (distinct (_ bv8688 14) g0) true))
(assert
 (and (distinct (_ bv15872 14) g0) true))
(assert
 (bvult a1 (_ bv8 4)))
(assert
 (bvult b1 (_ bv8 4)))
(assert
 (bvule a1 b1))
(assert
 (let (($x114 (= b1 (_ bv4 4))))
 (let ((?x115 (ite $x114 (_ bv6536 14) (ite (= b1 (_ bv5 4)) (_ bv8688 14) (ite (= b1 (_ bv6 4)) (_ bv15872 14) g0)))))
 (let (($x116 (= b1 (_ bv3 4))))
 (let (($x118 (= b1 (_ bv2 4))))
 (let (($x120 (= b1 (_ bv1 4))))
 (let (($x122 (= b1 (_ bv0 4))))
 (let ((?x123 (ite $x122 (_ bv4117 14) (ite $x120 (_ bv2723 14) (ite $x118 (_ bv5442 14) (ite $x116 (_ bv1644 14) ?x115))))))
 (let (($x100 (= a1 (_ bv4 4))))
 (let ((?x101 (ite $x100 (_ bv6536 14) (ite (= a1 (_ bv5 4)) (_ bv8688 14) (ite (= a1 (_ bv6 4)) (_ bv15872 14) g0)))))
 (let (($x102 (= a1 (_ bv3 4))))
 (let (($x104 (= a1 (_ bv2 4))))
 (let (($x106 (= a1 (_ bv1 4))))
 (let (($x108 (= a1 (_ bv0 4))))
 (let ((?x109 (ite $x108 (_ bv4117 14) (ite $x106 (_ bv2723 14) (ite $x104 (_ bv5442 14) (ite $x102 (_ bv1644 14) ?x101))))))
 (= g1 (ite or1 (bvor ?x109 ?x123) (bvand ?x109 ?x123))))))))))))))))))
(assert
 (= below1 (= (bvand g1 (_ bv8160 14)) (_ bv0 14))))
(assert
 (let (($x114 (= b1 (_ bv4 4))))
 (let (($x140 (ite $x114 false (ite (= b1 (_ bv5 4)) false (ite (= b1 (_ bv6 4)) false below0)))))
 (let (($x116 (= b1 (_ bv3 4))))
 (let (($x118 (= b1 (_ bv2 4))))
 (let (($x120 (= b1 (_ bv1 4))))
 (let (($x122 (= b1 (_ bv0 4))))
 (let (($x144 (ite $x122 false (ite $x120 false (ite $x118 false (ite $x116 false $x140))))))
 (let (($x100 (= a1 (_ bv4 4))))
 (let (($x133 (ite $x100 false (ite (= a1 (_ bv5 4)) false (ite (= a1 (_ bv6 4)) false below0)))))
 (let (($x102 (= a1 (_ bv3 4))))
 (let (($x104 (= a1 (_ bv2 4))))
 (let (($x106 (= a1 (_ bv1 4))))
 (let (($x108 (= a1 (_ bv0 4))))
 (let (($x137 (ite $x108 false (ite $x106 false (ite $x104 false (ite $x102 false $x133))))))
 (=> or1 (= $x137 $x144)))))))))))))))))
(assert
 (and (distinct g1 (_ bv0 14)) true))
(assert
 (and (distinct g1 (_ bv16383 14)) true))
(assert
 (and (distinct (_ bv4117 14) g1) true))
(assert
 (and (distinct (_ bv2723 14) g1) true))
(assert
 (and (distinct (_ bv5442 14) g1) true))
(assert
 (and (distinct (_ bv1644 14) g1) true))
(assert
 (and (distinct (_ bv6536 14) g1) true))
(assert
 (and (distinct (_ bv8688 14) g1) true))
(assert
 (and (distinct (_ bv15872 14) g1) true))
(assert
 (and (distinct g1 g0) true))
(assert
 (bvult a2 (_ bv9 4)))
(assert
 (bvult b2 (_ bv9 4)))
(assert
 (bvule a2 b2))
(assert
 (let (($x186 (= b2 (_ bv5 4))))
 (let ((?x187 (ite $x186 (_ bv8688 14) (ite (= b2 (_ bv6 4)) (_ bv15872 14) (ite (= b2 (_ bv7 4)) g0 g1)))))
 (let (($x188 (= b2 (_ bv4 4))))
 (let (($x190 (= b2 (_ bv3 4))))
 (let (($x192 (= b2 (_ bv2 4))))
 (let (($x194 (= b2 (_ bv1 4))))
 (let (($x196 (= b2 (_ bv0 4))))
 (let ((?x197 (ite $x196 (_ bv4117 14) (ite $x194 (_ bv2723 14) (ite $x192 (_ bv5442 14) (ite $x190 (_ bv1644 14) (ite $x188 (_ bv6536 14) ?x187)))))))
 (let (($x170 (= a2 (_ bv5 4))))
 (let ((?x171 (ite $x170 (_ bv8688 14) (ite (= a2 (_ bv6 4)) (_ bv15872 14) (ite (= a2 (_ bv7 4)) g0 g1)))))
 (let (($x172 (= a2 (_ bv4 4))))
 (let (($x174 (= a2 (_ bv3 4))))
 (let (($x176 (= a2 (_ bv2 4))))
 (let (($x178 (= a2 (_ bv1 4))))
 (let (($x180 (= a2 (_ bv0 4))))
 (let ((?x181 (ite $x180 (_ bv4117 14) (ite $x178 (_ bv2723 14) (ite $x176 (_ bv5442 14) (ite $x174 (_ bv1644 14) (ite $x172 (_ bv6536 14) ?x171)))))))
 (= g2 (ite or2 (bvor ?x181 ?x197) (bvand ?x181 ?x197))))))))))))))))))))
(assert
 (= below2 (= (bvand g2 (_ bv8160 14)) (_ bv0 14))))
(assert
 (let (($x186 (= b2 (_ bv5 4))))
 (let (($x215 (ite $x186 false (ite (= b2 (_ bv6 4)) false (ite (= b2 (_ bv7 4)) below0 below1)))))
 (let (($x188 (= b2 (_ bv4 4))))
 (let (($x190 (= b2 (_ bv3 4))))
 (let (($x192 (= b2 (_ bv2 4))))
 (let (($x194 (= b2 (_ bv1 4))))
 (let (($x219 (ite $x194 false (ite $x192 false (ite $x190 false (ite $x188 false $x215))))))
 (let (($x196 (= b2 (_ bv0 4))))
 (let (($x170 (= a2 (_ bv5 4))))
 (let (($x207 (ite $x170 false (ite (= a2 (_ bv6 4)) false (ite (= a2 (_ bv7 4)) below0 below1)))))
 (let (($x172 (= a2 (_ bv4 4))))
 (let (($x174 (= a2 (_ bv3 4))))
 (let (($x176 (= a2 (_ bv2 4))))
 (let (($x178 (= a2 (_ bv1 4))))
 (let (($x211 (ite $x178 false (ite $x176 false (ite $x174 false (ite $x172 false $x207))))))
 (let (($x180 (= a2 (_ bv0 4))))
 (=> or2 (= (ite $x180 false $x211) (ite $x196 false $x219))))))))))))))))))))
(assert
 (and (distinct g2 (_ bv0 14)) true))
(assert
 (and (distinct g2 (_ bv16383 14)) true))
(assert
 (and (distinct (_ bv4117 14) g2) true))
(assert
 (and (distinct (_ bv2723 14) g2) true))
(assert
 (and (distinct (_ bv5442 14) g2) true))
(assert
 (and (distinct (_ bv1644 14) g2) true))
(assert
 (and (distinct (_ bv6536 14) g2) true))
(assert
 (and (distinct (_ bv8688 14) g2) true))
(assert
 (and (distinct (_ bv15872 14) g2) true))
(assert
 (and (distinct g2 g0) true))
(assert
 (and (distinct g2 g1) true))
(assert
 (bvult a3 (_ bv10 4)))
(assert
 (bvult b3 (_ bv10 4)))
(assert
 (bvule a3 b3))
(assert
 (let (($x265 (= b3 (_ bv6 4))))
 (let ((?x266 (ite $x265 (_ bv15872 14) (ite (= b3 (_ bv7 4)) g0 (ite (= b3 (_ bv8 4)) g1 g2)))))
 (let (($x267 (= b3 (_ bv5 4))))
 (let (($x269 (= b3 (_ bv4 4))))
 (let (($x271 (= b3 (_ bv3 4))))
 (let (($x273 (= b3 (_ bv2 4))))
 (let (($x275 (= b3 (_ bv1 4))))
 (let ((?x276 (ite $x275 (_ bv2723 14) (ite $x273 (_ bv5442 14) (ite $x271 (_ bv1644 14) (ite $x269 (_ bv6536 14) (ite $x267 (_ bv8688 14) ?x266)))))))
 (let (($x277 (= b3 (_ bv0 4))))
 (let ((?x278 (ite $x277 (_ bv4117 14) ?x276)))
 (let (($x247 (= a3 (_ bv6 4))))
 (let ((?x248 (ite $x247 (_ bv15872 14) (ite (= a3 (_ bv7 4)) g0 (ite (= a3 (_ bv8 4)) g1 g2)))))
 (let (($x249 (= a3 (_ bv5 4))))
 (let (($x251 (= a3 (_ bv4 4))))
 (let (($x253 (= a3 (_ bv3 4))))
 (let (($x255 (= a3 (_ bv2 4))))
 (let (($x257 (= a3 (_ bv1 4))))
 (let ((?x258 (ite $x257 (_ bv2723 14) (ite $x255 (_ bv5442 14) (ite $x253 (_ bv1644 14) (ite $x251 (_ bv6536 14) (ite $x249 (_ bv8688 14) ?x248)))))))
 (let (($x259 (= a3 (_ bv0 4))))
 (let ((?x260 (ite $x259 (_ bv4117 14) ?x258)))
 (= g3 (ite or3 (bvor ?x260 ?x278) (bvand ?x260 ?x278))))))))))))))))))))))))
(assert
 (= below3 (= (bvand g3 (_ bv8160 14)) (_ bv0 14))))
(assert
 (let (($x265 (= b3 (_ bv6 4))))
 (let (($x297 (ite $x265 false (ite (= b3 (_ bv7 4)) below0 (ite (= b3 (_ bv8 4)) below1 below2)))))
 (let (($x267 (= b3 (_ bv5 4))))
 (let (($x269 (= b3 (_ bv4 4))))
 (let (($x271 (= b3 (_ bv3 4))))
 (let (($x273 (= b3 (_ bv2 4))))
 (let (($x301 (ite $x273 false (ite $x271 false (ite $x269 false (ite $x267 false $x297))))))
 (let (($x275 (= b3 (_ bv1 4))))
 (let (($x277 (= b3 (_ bv0 4))))
 (let (($x247 (= a3 (_ bv6 4))))
 (let (($x288 (ite $x247 false (ite (= a3 (_ bv7 4)) below0 (ite (= a3 (_ bv8 4)) below1 below2)))))
 (let (($x249 (= a3 (_ bv5 4))))
 (let (($x251 (= a3 (_ bv4 4))))
 (let (($x253 (= a3 (_ bv3 4))))
 (let (($x255 (= a3 (_ bv2 4))))
 (let (($x292 (ite $x255 false (ite $x253 false (ite $x251 false (ite $x249 false $x288))))))
 (let (($x257 (= a3 (_ bv1 4))))
 (let (($x259 (= a3 (_ bv0 4))))
 (let (($x304 (= (ite $x259 false (ite $x257 false $x292)) (ite $x277 false (ite $x275 false $x301)))))
 (=> or3 $x304)))))))))))))))))))))
(assert
 (and (distinct g3 (_ bv0 14)) true))
(assert
 (and (distinct g3 (_ bv16383 14)) true))
(assert
 (and (distinct (_ bv4117 14) g3) true))
(assert
 (and (distinct (_ bv2723 14) g3) true))
(assert
 (and (distinct (_ bv5442 14) g3) true))
(assert
 (and (distinct (_ bv1644 14) g3) true))
(assert
 (and (distinct (_ bv6536 14) g3) true))
(assert
 (and (distinct (_ bv8688 14) g3) true))
(assert
 (and (distinct (_ bv15872 14) g3) true))
(assert
 (and (distinct g3 g0) true))
(assert
 (and (distinct g3 g1) true))
(assert
 (and (distinct g3 g2) true))
(assert
 (bvult a4 (_ bv11 4)))
(assert
 (bvult b4 (_ bv11 4)))
(assert
 (bvule a4 b4))
(assert
 (let (($x351 (= b4 (_ bv7 4))))
 (let ((?x352 (ite $x351 g0 (ite (= b4 (_ bv8 4)) g1 (ite (= b4 (_ bv9 4)) g2 g3)))))
 (let (($x353 (= b4 (_ bv6 4))))
 (let (($x355 (= b4 (_ bv5 4))))
 (let (($x357 (= b4 (_ bv4 4))))
 (let (($x359 (= b4 (_ bv3 4))))
 (let (($x361 (= b4 (_ bv2 4))))
 (let ((?x362 (ite $x361 (_ bv5442 14) (ite $x359 (_ bv1644 14) (ite $x357 (_ bv6536 14) (ite $x355 (_ bv8688 14) (ite $x353 (_ bv15872 14) ?x352)))))))
 (let (($x363 (= b4 (_ bv1 4))))
 (let (($x365 (= b4 (_ bv0 4))))
 (let ((?x366 (ite $x365 (_ bv4117 14) (ite $x363 (_ bv2723 14) ?x362))))
 (let (($x331 (= a4 (_ bv7 4))))
 (let ((?x332 (ite $x331 g0 (ite (= a4 (_ bv8 4)) g1 (ite (= a4 (_ bv9 4)) g2 g3)))))
 (let (($x333 (= a4 (_ bv6 4))))
 (let (($x335 (= a4 (_ bv5 4))))
 (let (($x337 (= a4 (_ bv4 4))))
 (let (($x339 (= a4 (_ bv3 4))))
 (let (($x341 (= a4 (_ bv2 4))))
 (let ((?x342 (ite $x341 (_ bv5442 14) (ite $x339 (_ bv1644 14) (ite $x337 (_ bv6536 14) (ite $x335 (_ bv8688 14) (ite $x333 (_ bv15872 14) ?x332)))))))
 (let (($x343 (= a4 (_ bv1 4))))
 (let (($x345 (= a4 (_ bv0 4))))
 (let ((?x346 (ite $x345 (_ bv4117 14) (ite $x343 (_ bv2723 14) ?x342))))
 (= g4 (ite or4 (bvor ?x346 ?x366) (bvand ?x346 ?x366))))))))))))))))))))))))))
(assert
 (= below4 (= (bvand g4 (_ bv8160 14)) (_ bv0 14))))
(assert
 (let (($x351 (= b4 (_ bv7 4))))
 (let (($x386 (ite $x351 below0 (ite (= b4 (_ bv8 4)) below1 (ite (= b4 (_ bv9 4)) below2 below3)))))
 (let (($x353 (= b4 (_ bv6 4))))
 (let (($x355 (= b4 (_ bv5 4))))
 (let (($x357 (= b4 (_ bv4 4))))
 (let (($x359 (= b4 (_ bv3 4))))
 (let (($x390 (ite $x359 false (ite $x357 false (ite $x355 false (ite $x353 false $x386))))))
 (let (($x361 (= b4 (_ bv2 4))))
 (let (($x363 (= b4 (_ bv1 4))))
 (let (($x365 (= b4 (_ bv0 4))))
 (let (($x331 (= a4 (_ bv7 4))))
 (let (($x376 (ite $x331 below0 (ite (= a4 (_ bv8 4)) below1 (ite (= a4 (_ bv9 4)) below2 below3)))))
 (let (($x333 (= a4 (_ bv6 4))))
 (let (($x335 (= a4 (_ bv5 4))))
 (let (($x337 (= a4 (_ bv4 4))))
 (let (($x339 (= a4 (_ bv3 4))))
 (let (($x380 (ite $x339 false (ite $x337 false (ite $x335 false (ite $x333 false $x376))))))
 (let (($x341 (= a4 (_ bv2 4))))
 (let (($x343 (= a4 (_ bv1 4))))
 (let (($x345 (= a4 (_ bv0 4))))
 (let (($x394 (= (ite $x345 false (ite $x343 false (ite $x341 false $x380))) (ite $x365 false (ite $x363 false (ite $x361 false $x390))))))
 (=> or4 $x394)))))))))))))))))))))))
(assert
 (and (distinct g4 (_ bv0 14)) true))
(assert
 (and (distinct g4 (_ bv16383 14)) true))
(assert
 (and (distinct (_ bv4117 14) g4) true))
(assert
 (and (distinct (_ bv2723 14) g4) true))
(assert
 (and (distinct (_ bv5442 14) g4) true))
(assert
 (and (distinct (_ bv1644 14) g4) true))
(assert
 (and (distinct (_ bv6536 14) g4) true))
(assert
 (and (distinct (_ bv8688 14) g4) true))
(assert
 (and (distinct (_ bv15872 14) g4) true))
(assert
 (and (distinct g4 g0) true))
(assert
 (and (distinct g4 g1) true))
(assert
 (and (distinct g4 g2) true))
(assert
 (and (distinct g4 g3) true))
(assert
 (bvult a5 (_ bv12 4)))
(assert
 (bvult b5 (_ bv12 4)))
(assert
 (bvule a5 b5))
(assert
 (let (($x444 (= b5 (_ bv8 4))))
 (let ((?x445 (ite $x444 g1 (ite (= b5 (_ bv9 4)) g2 (ite (= b5 (_ bv10 4)) g3 g4)))))
 (let (($x446 (= b5 (_ bv7 4))))
 (let (($x448 (= b5 (_ bv6 4))))
 (let (($x450 (= b5 (_ bv5 4))))
 (let (($x452 (= b5 (_ bv4 4))))
 (let (($x454 (= b5 (_ bv3 4))))
 (let ((?x455 (ite $x454 (_ bv1644 14) (ite $x452 (_ bv6536 14) (ite $x450 (_ bv8688 14) (ite $x448 (_ bv15872 14) (ite $x446 g0 ?x445)))))))
 (let (($x456 (= b5 (_ bv2 4))))
 (let (($x458 (= b5 (_ bv1 4))))
 (let (($x460 (= b5 (_ bv0 4))))
 (let ((?x461 (ite $x460 (_ bv4117 14) (ite $x458 (_ bv2723 14) (ite $x456 (_ bv5442 14) ?x455)))))
 (let (($x422 (= a5 (_ bv8 4))))
 (let ((?x423 (ite $x422 g1 (ite (= a5 (_ bv9 4)) g2 (ite (= a5 (_ bv10 4)) g3 g4)))))
 (let (($x424 (= a5 (_ bv7 4))))
 (let (($x426 (= a5 (_ bv6 4))))
 (let (($x428 (= a5 (_ bv5 4))))
 (let (($x430 (= a5 (_ bv4 4))))
 (let (($x432 (= a5 (_ bv3 4))))
 (let ((?x433 (ite $x432 (_ bv1644 14) (ite $x430 (_ bv6536 14) (ite $x428 (_ bv8688 14) (ite $x426 (_ bv15872 14) (ite $x424 g0 ?x423)))))))
 (let (($x434 (= a5 (_ bv2 4))))
 (let (($x436 (= a5 (_ bv1 4))))
 (let (($x438 (= a5 (_ bv0 4))))
 (let ((?x439 (ite $x438 (_ bv4117 14) (ite $x436 (_ bv2723 14) (ite $x434 (_ bv5442 14) ?x433)))))
 (= g5 (ite or5 (bvor ?x439 ?x461) (bvand ?x439 ?x461))))))))))))))))))))))))))))
(assert
 (= below5 (= (bvand g5 (_ bv8160 14)) (_ bv0 14))))
(assert
 (let (($x444 (= b5 (_ bv8 4))))
 (let (($x482 (ite $x444 below1 (ite (= b5 (_ bv9 4)) below2 (ite (= b5 (_ bv10 4)) below3 below4)))))
 (let (($x446 (= b5 (_ bv7 4))))
 (let (($x448 (= b5 (_ bv6 4))))
 (let (($x450 (= b5 (_ bv5 4))))
 (let (($x452 (= b5 (_ bv4 4))))
 (let (($x486 (ite $x452 false (ite $x450 false (ite $x448 false (ite $x446 below0 $x482))))))
 (let (($x454 (= b5 (_ bv3 4))))
 (let (($x456 (= b5 (_ bv2 4))))
 (let (($x458 (= b5 (_ bv1 4))))
 (let (($x460 (= b5 (_ bv0 4))))
 (let (($x490 (ite $x460 false (ite $x458 false (ite $x456 false (ite $x454 false $x486))))))
 (let (($x422 (= a5 (_ bv8 4))))
 (let (($x471 (ite $x422 below1 (ite (= a5 (_ bv9 4)) below2 (ite (= a5 (_ bv10 4)) below3 below4)))))
 (let (($x424 (= a5 (_ bv7 4))))
 (let (($x426 (= a5 (_ bv6 4))))
 (let (($x428 (= a5 (_ bv5 4))))
 (let (($x430 (= a5 (_ bv4 4))))
 (let (($x475 (ite $x430 false (ite $x428 false (ite $x426 false (ite $x424 below0 $x471))))))
 (let (($x432 (= a5 (_ bv3 4))))
 (let (($x434 (= a5 (_ bv2 4))))
 (let (($x436 (= a5 (_ bv1 4))))
 (let (($x438 (= a5 (_ bv0 4))))
 (let (($x479 (ite $x438 false (ite $x436 false (ite $x434 false (ite $x432 false $x475))))))
 (=> or5 (= $x479 $x490)))))))))))))))))))))))))))
(assert
 (and (distinct g5 (_ bv0 14)) true))
(assert
 (and (distinct g5 (_ bv16383 14)) true))
(assert
 (and (distinct (_ bv4117 14) g5) true))
(assert
 (and (distinct (_ bv2723 14) g5) true))
(assert
 (and (distinct (_ bv5442 14) g5) true))
(assert
 (and (distinct (_ bv1644 14) g5) true))
(assert
 (and (distinct (_ bv6536 14) g5) true))
(assert
 (and (distinct (_ bv8688 14) g5) true))
(assert
 (and (distinct (_ bv15872 14) g5) true))
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
 (bvult a6 (_ bv13 4)))
(assert
 (bvult b6 (_ bv13 4)))
(assert
 (bvule a6 b6))
(assert
 (let (($x544 (= b6 (_ bv9 4))))
 (let ((?x545 (ite $x544 g2 (ite (= b6 (_ bv10 4)) g3 (ite (= b6 (_ bv11 4)) g4 g5)))))
 (let (($x546 (= b6 (_ bv8 4))))
 (let (($x548 (= b6 (_ bv7 4))))
 (let (($x550 (= b6 (_ bv6 4))))
 (let (($x552 (= b6 (_ bv5 4))))
 (let (($x554 (= b6 (_ bv4 4))))
 (let ((?x555 (ite $x554 (_ bv6536 14) (ite $x552 (_ bv8688 14) (ite $x550 (_ bv15872 14) (ite $x548 g0 (ite $x546 g1 ?x545)))))))
 (let (($x556 (= b6 (_ bv3 4))))
 (let (($x558 (= b6 (_ bv2 4))))
 (let (($x560 (= b6 (_ bv1 4))))
 (let (($x562 (= b6 (_ bv0 4))))
 (let ((?x563 (ite $x562 (_ bv4117 14) (ite $x560 (_ bv2723 14) (ite $x558 (_ bv5442 14) (ite $x556 (_ bv1644 14) ?x555))))))
 (let (($x520 (= a6 (_ bv9 4))))
 (let ((?x521 (ite $x520 g2 (ite (= a6 (_ bv10 4)) g3 (ite (= a6 (_ bv11 4)) g4 g5)))))
 (let (($x522 (= a6 (_ bv8 4))))
 (let (($x524 (= a6 (_ bv7 4))))
 (let (($x526 (= a6 (_ bv6 4))))
 (let (($x528 (= a6 (_ bv5 4))))
 (let (($x530 (= a6 (_ bv4 4))))
 (let ((?x531 (ite $x530 (_ bv6536 14) (ite $x528 (_ bv8688 14) (ite $x526 (_ bv15872 14) (ite $x524 g0 (ite $x522 g1 ?x521)))))))
 (let (($x532 (= a6 (_ bv3 4))))
 (let (($x534 (= a6 (_ bv2 4))))
 (let (($x536 (= a6 (_ bv1 4))))
 (let (($x538 (= a6 (_ bv0 4))))
 (let ((?x539 (ite $x538 (_ bv4117 14) (ite $x536 (_ bv2723 14) (ite $x534 (_ bv5442 14) (ite $x532 (_ bv1644 14) ?x531))))))
 (= g6 (ite or6 (bvor ?x539 ?x563) (bvand ?x539 ?x563))))))))))))))))))))))))))))))
(assert
 (= below6 (= (bvand g6 (_ bv8160 14)) (_ bv0 14))))
(assert
 (let (($x544 (= b6 (_ bv9 4))))
 (let (($x585 (ite $x544 below2 (ite (= b6 (_ bv10 4)) below3 (ite (= b6 (_ bv11 4)) below4 below5)))))
 (let (($x546 (= b6 (_ bv8 4))))
 (let (($x548 (= b6 (_ bv7 4))))
 (let (($x550 (= b6 (_ bv6 4))))
 (let (($x552 (= b6 (_ bv5 4))))
 (let (($x589 (ite $x552 false (ite $x550 false (ite $x548 below0 (ite $x546 below1 $x585))))))
 (let (($x554 (= b6 (_ bv4 4))))
 (let (($x556 (= b6 (_ bv3 4))))
 (let (($x558 (= b6 (_ bv2 4))))
 (let (($x560 (= b6 (_ bv1 4))))
 (let (($x593 (ite $x560 false (ite $x558 false (ite $x556 false (ite $x554 false $x589))))))
 (let (($x562 (= b6 (_ bv0 4))))
 (let (($x520 (= a6 (_ bv9 4))))
 (let (($x573 (ite $x520 below2 (ite (= a6 (_ bv10 4)) below3 (ite (= a6 (_ bv11 4)) below4 below5)))))
 (let (($x522 (= a6 (_ bv8 4))))
 (let (($x524 (= a6 (_ bv7 4))))
 (let (($x526 (= a6 (_ bv6 4))))
 (let (($x528 (= a6 (_ bv5 4))))
 (let (($x577 (ite $x528 false (ite $x526 false (ite $x524 below0 (ite $x522 below1 $x573))))))
 (let (($x530 (= a6 (_ bv4 4))))
 (let (($x532 (= a6 (_ bv3 4))))
 (let (($x534 (= a6 (_ bv2 4))))
 (let (($x536 (= a6 (_ bv1 4))))
 (let (($x581 (ite $x536 false (ite $x534 false (ite $x532 false (ite $x530 false $x577))))))
 (let (($x538 (= a6 (_ bv0 4))))
 (=> or6 (= (ite $x538 false $x581) (ite $x562 false $x593))))))))))))))))))))))))))))))
(assert
 (and (distinct g6 (_ bv0 14)) true))
(assert
 (and (distinct g6 (_ bv16383 14)) true))
(assert
 (and (distinct (_ bv4117 14) g6) true))
(assert
 (and (distinct (_ bv2723 14) g6) true))
(assert
 (and (distinct (_ bv5442 14) g6) true))
(assert
 (and (distinct (_ bv1644 14) g6) true))
(assert
 (and (distinct (_ bv6536 14) g6) true))
(assert
 (and (distinct (_ bv8688 14) g6) true))
(assert
 (and (distinct (_ bv15872 14) g6) true))
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
 (bvult a7 (_ bv14 4)))
(assert
 (bvult b7 (_ bv14 4)))
(assert
 (bvule a7 b7))
(assert
 (let (($x651 (= b7 (_ bv10 4))))
 (let ((?x652 (ite $x651 g3 (ite (= b7 (_ bv11 4)) g4 (ite (= b7 (_ bv12 4)) g5 g6)))))
 (let (($x653 (= b7 (_ bv9 4))))
 (let (($x655 (= b7 (_ bv8 4))))
 (let (($x657 (= b7 (_ bv7 4))))
 (let (($x659 (= b7 (_ bv6 4))))
 (let (($x661 (= b7 (_ bv5 4))))
 (let ((?x662 (ite $x661 (_ bv8688 14) (ite $x659 (_ bv15872 14) (ite $x657 g0 (ite $x655 g1 (ite $x653 g2 ?x652)))))))
 (let (($x663 (= b7 (_ bv4 4))))
 (let (($x665 (= b7 (_ bv3 4))))
 (let (($x667 (= b7 (_ bv2 4))))
 (let (($x669 (= b7 (_ bv1 4))))
 (let (($x671 (= b7 (_ bv0 4))))
 (let ((?x672 (ite $x671 (_ bv4117 14) (ite $x669 (_ bv2723 14) (ite $x667 (_ bv5442 14) (ite $x665 (_ bv1644 14) (ite $x663 (_ bv6536 14) ?x662)))))))
 (let (($x625 (= a7 (_ bv10 4))))
 (let ((?x626 (ite $x625 g3 (ite (= a7 (_ bv11 4)) g4 (ite (= a7 (_ bv12 4)) g5 g6)))))
 (let (($x627 (= a7 (_ bv9 4))))
 (let (($x629 (= a7 (_ bv8 4))))
 (let (($x631 (= a7 (_ bv7 4))))
 (let (($x633 (= a7 (_ bv6 4))))
 (let (($x635 (= a7 (_ bv5 4))))
 (let ((?x636 (ite $x635 (_ bv8688 14) (ite $x633 (_ bv15872 14) (ite $x631 g0 (ite $x629 g1 (ite $x627 g2 ?x626)))))))
 (let (($x637 (= a7 (_ bv4 4))))
 (let (($x639 (= a7 (_ bv3 4))))
 (let (($x641 (= a7 (_ bv2 4))))
 (let (($x643 (= a7 (_ bv1 4))))
 (let (($x645 (= a7 (_ bv0 4))))
 (let ((?x646 (ite $x645 (_ bv4117 14) (ite $x643 (_ bv2723 14) (ite $x641 (_ bv5442 14) (ite $x639 (_ bv1644 14) (ite $x637 (_ bv6536 14) ?x636)))))))
 (= g7 (ite or7 (bvor ?x646 ?x672) (bvand ?x646 ?x672))))))))))))))))))))))))))))))))
(assert
 (= below7 (= (bvand g7 (_ bv8160 14)) (_ bv0 14))))
(assert
 (let (($x651 (= b7 (_ bv10 4))))
 (let (($x695 (ite $x651 below3 (ite (= b7 (_ bv11 4)) below4 (ite (= b7 (_ bv12 4)) below5 below6)))))
 (let (($x653 (= b7 (_ bv9 4))))
 (let (($x655 (= b7 (_ bv8 4))))
 (let (($x657 (= b7 (_ bv7 4))))
 (let (($x659 (= b7 (_ bv6 4))))
 (let (($x699 (ite $x659 false (ite $x657 below0 (ite $x655 below1 (ite $x653 below2 $x695))))))
 (let (($x661 (= b7 (_ bv5 4))))
 (let (($x663 (= b7 (_ bv4 4))))
 (let (($x665 (= b7 (_ bv3 4))))
 (let (($x667 (= b7 (_ bv2 4))))
 (let (($x703 (ite $x667 false (ite $x665 false (ite $x663 false (ite $x661 false $x699))))))
 (let (($x669 (= b7 (_ bv1 4))))
 (let (($x671 (= b7 (_ bv0 4))))
 (let (($x625 (= a7 (_ bv10 4))))
 (let (($x682 (ite $x625 below3 (ite (= a7 (_ bv11 4)) below4 (ite (= a7 (_ bv12 4)) below5 below6)))))
 (let (($x627 (= a7 (_ bv9 4))))
 (let (($x629 (= a7 (_ bv8 4))))
 (let (($x631 (= a7 (_ bv7 4))))
 (let (($x633 (= a7 (_ bv6 4))))
 (let (($x686 (ite $x633 false (ite $x631 below0 (ite $x629 below1 (ite $x627 below2 $x682))))))
 (let (($x635 (= a7 (_ bv5 4))))
 (let (($x637 (= a7 (_ bv4 4))))
 (let (($x639 (= a7 (_ bv3 4))))
 (let (($x641 (= a7 (_ bv2 4))))
 (let (($x690 (ite $x641 false (ite $x639 false (ite $x637 false (ite $x635 false $x686))))))
 (let (($x643 (= a7 (_ bv1 4))))
 (let (($x645 (= a7 (_ bv0 4))))
 (let (($x706 (= (ite $x645 false (ite $x643 false $x690)) (ite $x671 false (ite $x669 false $x703)))))
 (=> or7 $x706)))))))))))))))))))))))))))))))
(assert
 (and (distinct g7 (_ bv0 14)) true))
(assert
 (and (distinct g7 (_ bv16383 14)) true))
(assert
 (and (distinct (_ bv4117 14) g7) true))
(assert
 (and (distinct (_ bv2723 14) g7) true))
(assert
 (and (distinct (_ bv5442 14) g7) true))
(assert
 (and (distinct (_ bv1644 14) g7) true))
(assert
 (and (distinct (_ bv6536 14) g7) true))
(assert
 (and (distinct (_ bv8688 14) g7) true))
(assert
 (and (distinct (_ bv15872 14) g7) true))
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
 (= (_ bv8223 14) g7))
(assert
 (or (and (not or0) (not below0)) (and (not or1) (not below1)) (and (not or2) (not below2)) (and (not or3) (not below3)) (and (not or4) (not below4)) (and (not or5) (not below5)) (and (not or6) (not below6)) (and (not or7) (not below7))))
(assert
 (or (or (= a1 (_ bv7 4)) (= b1 (_ bv7 4))) (or (= a2 (_ bv7 4)) (= b2 (_ bv7 4))) (or (= a3 (_ bv7 4)) (= b3 (_ bv7 4))) (or (= a4 (_ bv7 4)) (= b4 (_ bv7 4))) (or (= a5 (_ bv7 4)) (= b5 (_ bv7 4))) (or (= a6 (_ bv7 4)) (= b6 (_ bv7 4))) (or (= a7 (_ bv7 4)) (= b7 (_ bv7 4)))))
(assert
 (or (or (= a2 (_ bv8 4)) (= b2 (_ bv8 4))) (or (= a3 (_ bv8 4)) (= b3 (_ bv8 4))) (or (= a4 (_ bv8 4)) (= b4 (_ bv8 4))) (or (= a5 (_ bv8 4)) (= b5 (_ bv8 4))) (or (= a6 (_ bv8 4)) (= b6 (_ bv8 4))) (or (= a7 (_ bv8 4)) (= b7 (_ bv8 4)))))
(assert
 (or (or (= a3 (_ bv9 4)) (= b3 (_ bv9 4))) (or (= a4 (_ bv9 4)) (= b4 (_ bv9 4))) (or (= a5 (_ bv9 4)) (= b5 (_ bv9 4))) (or (= a6 (_ bv9 4)) (= b6 (_ bv9 4))) (or (= a7 (_ bv9 4)) (= b7 (_ bv9 4)))))
(assert
 (or (or (= a4 (_ bv10 4)) (= b4 (_ bv10 4))) (or (= a5 (_ bv10 4)) (= b5 (_ bv10 4))) (or (= a6 (_ bv10 4)) (= b6 (_ bv10 4))) (or (= a7 (_ bv10 4)) (= b7 (_ bv10 4)))))
(assert
 (or (or (= a5 (_ bv11 4)) (= b5 (_ bv11 4))) (or (= a6 (_ bv11 4)) (= b6 (_ bv11 4))) (or (= a7 (_ bv11 4)) (= b7 (_ bv11 4)))))
(assert
 (or (or (= a6 (_ bv12 4)) (= b6 (_ bv12 4))) (or (= a7 (_ bv12 4)) (= b7 (_ bv12 4)))))
(assert
 (or (or (= a7 (_ bv13 4)) (= b7 (_ bv13 4)))))
(assert
 (let ((?x802 (concat (concat (ite or1 (_ bv0 1) (_ bv1 1)) a1) b1)))
 (let (($x752 (= b1 (_ bv7 4))))
 (let (($x751 (= a1 (_ bv7 4))))
 (or $x751 $x752 (bvule (concat (concat (ite or0 (_ bv0 1) (_ bv1 1)) a0) b0) ?x802))))))
(assert
 (let ((?x810 (concat (concat (ite or2 (_ bv0 1) (_ bv1 1)) a2) b2)))
 (let ((?x802 (concat (concat (ite or1 (_ bv0 1) (_ bv1 1)) a1) b1)))
 (let (($x762 (= b2 (_ bv8 4))))
 (let (($x761 (= a2 (_ bv8 4))))
 (or $x761 $x762 (bvule ?x802 ?x810)))))))
(assert
 (let ((?x815 (concat (concat (ite or3 (_ bv0 1) (_ bv1 1)) a3) b3)))
 (let ((?x810 (concat (concat (ite or2 (_ bv0 1) (_ bv1 1)) a2) b2)))
 (let (($x771 (= b3 (_ bv9 4))))
 (let (($x770 (= a3 (_ bv9 4))))
 (or $x770 $x771 (bvule ?x810 ?x815)))))))
(assert
 (let ((?x820 (concat (concat (ite or4 (_ bv0 1) (_ bv1 1)) a4) b4)))
 (let ((?x815 (concat (concat (ite or3 (_ bv0 1) (_ bv1 1)) a3) b3)))
 (let (($x779 (= b4 (_ bv10 4))))
 (let (($x778 (= a4 (_ bv10 4))))
 (or $x778 $x779 (bvule ?x815 ?x820)))))))
(assert
 (let ((?x825 (concat (concat (ite or5 (_ bv0 1) (_ bv1 1)) a5) b5)))
 (let ((?x820 (concat (concat (ite or4 (_ bv0 1) (_ bv1 1)) a4) b4)))
 (let (($x786 (= b5 (_ bv11 4))))
 (let (($x785 (= a5 (_ bv11 4))))
 (or $x785 $x786 (bvule ?x820 ?x825)))))))
(assert
 (let ((?x830 (concat (concat (ite or6 (_ bv0 1) (_ bv1 1)) a6) b6)))
 (let ((?x825 (concat (concat (ite or5 (_ bv0 1) (_ bv1 1)) a5) b5)))
 (let (($x792 (= b6 (_ bv12 4))))
 (let (($x791 (= a6 (_ bv12 4))))
 (or $x791 $x792 (bvule ?x825 ?x830)))))))
(assert
 (let ((?x835 (concat (concat (ite or7 (_ bv0 1) (_ bv1 1)) a7) b7)))
(let ((?x830 (concat (concat (ite or6 (_ bv0 1) (_ bv1 1)) a6) b6)))
(let (($x797 (= b7 (_ bv13 4))))
(let (($x796 (= a7 (_ bv13 4))))
(or $x796 $x797 (bvule ?x830 ?x835)))))))
(check-sat)
