; benchmark generated from python API
(set-info :status unknown)
(declare-fun a0 () (_ BitVec 3))
(declare-fun b0 () (_ BitVec 3))
(declare-fun or0 () Bool)
(declare-fun g0 () (_ BitVec 3))
(declare-fun below0 () Bool)
(assert
 (bvult a0 (_ bv6 3)))
(assert
 (bvult b0 (_ bv6 3)))
(assert
 (bvule a0 b0))
(assert
 (let (($x36 (= b0 (_ bv2 3))))
 (let ((?x37 (ite $x36 (_ bv6 3) (ite (= b0 (_ bv3 3)) (_ bv6 3) (ite (= b0 (_ bv4 3)) (_ bv6 3) (_ bv6 3))))))
 (let (($x38 (= b0 (_ bv1 3))))
 (let (($x40 (= b0 (_ bv0 3))))
 (let ((?x41 (ite $x40 (_ bv3 3) (ite $x38 (_ bv5 3) ?x37))))
 (let (($x24 (= a0 (_ bv2 3))))
 (let ((?x25 (ite $x24 (_ bv6 3) (ite (= a0 (_ bv3 3)) (_ bv6 3) (ite (= a0 (_ bv4 3)) (_ bv6 3) (_ bv6 3))))))
 (let (($x27 (= a0 (_ bv1 3))))
 (let (($x30 (= a0 (_ bv0 3))))
 (let ((?x31 (ite $x30 (_ bv3 3) (ite $x27 (_ bv5 3) ?x25))))
 (= g0 (ite or0 (bvor ?x31 ?x41) (bvand ?x31 ?x41))))))))))))))
(assert
 (= below0 (= (bvand g0 (_ bv6 3)) (_ bv0 3))))
(assert
 (let (($x36 (= b0 (_ bv2 3))))
 (let (($x56 (ite $x36 false (ite (= b0 (_ bv3 3)) false (ite (= b0 (_ bv4 3)) false false)))))
 (let (($x38 (= b0 (_ bv1 3))))
 (let (($x40 (= b0 (_ bv0 3))))
 (let (($x24 (= a0 (_ bv2 3))))
 (let (($x51 (ite $x24 false (ite (= a0 (_ bv3 3)) false (ite (= a0 (_ bv4 3)) false false)))))
 (let (($x27 (= a0 (_ bv1 3))))
 (let (($x30 (= a0 (_ bv0 3))))
 (let (($x59 (= (ite $x30 false (ite $x27 false $x51)) (ite $x40 false (ite $x38 false $x56)))))
 (=> or0 $x59)))))))))))
(assert
 (= (_ bv1 3) g0))
(assert
 (or (and (not or0) (not below0))))
(check-sat)
