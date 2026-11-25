; benchmark generated from python API
(set-info :status unknown)
(declare-fun signature_0_0_0 () Bool)
(declare-fun signature_0_0_1 () Bool)
(declare-fun signature_0_0_2 () Bool)
(declare-fun signature_0_0_3 () Bool)
(declare-fun t_0_0 () (_ BitVec 6))
(declare-fun signature_0_1_0 () Bool)
(declare-fun signature_0_1_1 () Bool)
(declare-fun signature_0_1_2 () Bool)
(declare-fun signature_0_1_3 () Bool)
(declare-fun t_0_1 () (_ BitVec 6))
(declare-fun g_0 () (_ BitVec 6))
(declare-fun signature_1_0_0 () Bool)
(declare-fun signature_1_0_1 () Bool)
(declare-fun signature_1_0_2 () Bool)
(declare-fun signature_1_0_3 () Bool)
(declare-fun t_1_0 () (_ BitVec 6))
(declare-fun signature_1_1_0 () Bool)
(declare-fun signature_1_1_1 () Bool)
(declare-fun signature_1_1_2 () Bool)
(declare-fun signature_1_1_3 () Bool)
(declare-fun t_1_1 () (_ BitVec 6))
(declare-fun g_1 () (_ BitVec 6))
(declare-fun cover_1_0_1 () Bool)
(declare-fun cover_1_0_3 () Bool)
(declare-fun cover_1_0_4 () Bool)
(declare-fun cover_1_1_0 () Bool)
(declare-fun cover_1_1_2 () Bool)
(declare-fun cover_1_1_4 () Bool)
(assert
 (let ((?x21 (concat (ite signature_0_0_3 (_ bv1 1) (_ bv0 1)) (ite signature_0_0_2 (_ bv1 1) (_ bv0 1)))))
 (let ((?x23 (concat (concat ?x21 (ite signature_0_0_1 (_ bv1 1) (_ bv0 1))) (ite signature_0_0_0 (_ bv1 1) (_ bv0 1)))))
 (and (distinct ?x23 (_ bv0 4)) true))))
(assert
 (let ((?x21 (concat (ite signature_0_0_3 (_ bv1 1) (_ bv0 1)) (ite signature_0_0_2 (_ bv1 1) (_ bv0 1)))))
 (let ((?x23 (concat (concat ?x21 (ite signature_0_0_1 (_ bv1 1) (_ bv0 1))) (ite signature_0_0_0 (_ bv1 1) (_ bv0 1)))))
 (let ((?x24 ((_ zero_extend 2) ?x23)))
 (let ((?x34 (bvand (bvand (_ bv63 6) (ite (= (bvand (_ bv21 6) ?x24) ?x24) (_ bv21 6) (_ bv63 6))) (ite (= (bvand (_ bv35 6) ?x24) ?x24) (_ bv35 6) (_ bv63 6)))))
 (let ((?x42 (bvand (bvand ?x34 (ite (= (bvand (_ bv26 6) ?x24) ?x24) (_ bv26 6) (_ bv63 6))) (ite (= (bvand (_ bv44 6) ?x24) ?x24) (_ bv44 6) (_ bv63 6)))))
 (= t_0_0 ?x42)))))))
(assert
 (let ((?x21 (concat (ite signature_0_0_3 (_ bv1 1) (_ bv0 1)) (ite signature_0_0_2 (_ bv1 1) (_ bv0 1)))))
 (let ((?x23 (concat (concat ?x21 (ite signature_0_0_1 (_ bv1 1) (_ bv0 1))) (ite signature_0_0_0 (_ bv1 1) (_ bv0 1)))))
 (let ((?x24 ((_ zero_extend 2) ?x23)))
 (= (bvand t_0_0 (_ bv15 6)) ?x24)))))
(assert
 (let ((?x55 (concat (ite signature_0_1_3 (_ bv1 1) (_ bv0 1)) (ite signature_0_1_2 (_ bv1 1) (_ bv0 1)))))
 (let ((?x57 (concat (concat ?x55 (ite signature_0_1_1 (_ bv1 1) (_ bv0 1))) (ite signature_0_1_0 (_ bv1 1) (_ bv0 1)))))
 (and (distinct ?x57 (_ bv0 4)) true))))
(assert
 (let ((?x55 (concat (ite signature_0_1_3 (_ bv1 1) (_ bv0 1)) (ite signature_0_1_2 (_ bv1 1) (_ bv0 1)))))
 (let ((?x57 (concat (concat ?x55 (ite signature_0_1_1 (_ bv1 1) (_ bv0 1))) (ite signature_0_1_0 (_ bv1 1) (_ bv0 1)))))
 (let ((?x58 ((_ zero_extend 2) ?x57)))
 (let ((?x67 (bvand (bvand (_ bv63 6) (ite (= (bvand (_ bv21 6) ?x58) ?x58) (_ bv21 6) (_ bv63 6))) (ite (= (bvand (_ bv35 6) ?x58) ?x58) (_ bv35 6) (_ bv63 6)))))
 (let ((?x75 (bvand (bvand ?x67 (ite (= (bvand (_ bv26 6) ?x58) ?x58) (_ bv26 6) (_ bv63 6))) (ite (= (bvand (_ bv44 6) ?x58) ?x58) (_ bv44 6) (_ bv63 6)))))
 (= t_0_1 ?x75)))))))
(assert
 (let ((?x55 (concat (ite signature_0_1_3 (_ bv1 1) (_ bv0 1)) (ite signature_0_1_2 (_ bv1 1) (_ bv0 1)))))
 (let ((?x57 (concat (concat ?x55 (ite signature_0_1_1 (_ bv1 1) (_ bv0 1))) (ite signature_0_1_0 (_ bv1 1) (_ bv0 1)))))
 (let ((?x58 ((_ zero_extend 2) ?x57)))
 (= (bvand t_0_1 (_ bv15 6)) ?x58)))))
(assert
 (let ((?x55 (concat (ite signature_0_1_3 (_ bv1 1) (_ bv0 1)) (ite signature_0_1_2 (_ bv1 1) (_ bv0 1)))))
 (let ((?x57 (concat (concat ?x55 (ite signature_0_1_1 (_ bv1 1) (_ bv0 1))) (ite signature_0_1_0 (_ bv1 1) (_ bv0 1)))))
 (let ((?x21 (concat (ite signature_0_0_3 (_ bv1 1) (_ bv0 1)) (ite signature_0_0_2 (_ bv1 1) (_ bv0 1)))))
 (let ((?x23 (concat (concat ?x21 (ite signature_0_0_1 (_ bv1 1) (_ bv0 1))) (ite signature_0_0_0 (_ bv1 1) (_ bv0 1)))))
 (and (distinct (bvand ?x23 (bvnot ?x57)) (_ bv0 4)) true))))))
(assert
 (let ((?x21 (concat (ite signature_0_0_3 (_ bv1 1) (_ bv0 1)) (ite signature_0_0_2 (_ bv1 1) (_ bv0 1)))))
 (let ((?x23 (concat (concat ?x21 (ite signature_0_0_1 (_ bv1 1) (_ bv0 1))) (ite signature_0_0_0 (_ bv1 1) (_ bv0 1)))))
 (let ((?x55 (concat (ite signature_0_1_3 (_ bv1 1) (_ bv0 1)) (ite signature_0_1_2 (_ bv1 1) (_ bv0 1)))))
 (let ((?x57 (concat (concat ?x55 (ite signature_0_1_1 (_ bv1 1) (_ bv0 1))) (ite signature_0_1_0 (_ bv1 1) (_ bv0 1)))))
 (and (distinct (bvand ?x57 (bvnot ?x23)) (_ bv0 4)) true))))))
(assert
 (let ((?x55 (concat (ite signature_0_1_3 (_ bv1 1) (_ bv0 1)) (ite signature_0_1_2 (_ bv1 1) (_ bv0 1)))))
 (let ((?x57 (concat (concat ?x55 (ite signature_0_1_1 (_ bv1 1) (_ bv0 1))) (ite signature_0_1_0 (_ bv1 1) (_ bv0 1)))))
 (let ((?x21 (concat (ite signature_0_0_3 (_ bv1 1) (_ bv0 1)) (ite signature_0_0_2 (_ bv1 1) (_ bv0 1)))))
 (let ((?x23 (concat (concat ?x21 (ite signature_0_0_1 (_ bv1 1) (_ bv0 1))) (ite signature_0_0_0 (_ bv1 1) (_ bv0 1)))))
 (bvult ?x23 ?x57))))))
(assert
 (= g_0 (bvor t_0_0 t_0_1)))
(assert
 (let ((?x98 (concat (ite signature_1_0_3 (_ bv1 1) (_ bv0 1)) (ite signature_1_0_2 (_ bv1 1) (_ bv0 1)))))
 (let ((?x100 (concat (concat ?x98 (ite signature_1_0_1 (_ bv1 1) (_ bv0 1))) (ite signature_1_0_0 (_ bv1 1) (_ bv0 1)))))
 (and (distinct ?x100 (_ bv0 4)) true))))
(assert
 (let ((?x98 (concat (ite signature_1_0_3 (_ bv1 1) (_ bv0 1)) (ite signature_1_0_2 (_ bv1 1) (_ bv0 1)))))
 (let ((?x100 (concat (concat ?x98 (ite signature_1_0_1 (_ bv1 1) (_ bv0 1))) (ite signature_1_0_0 (_ bv1 1) (_ bv0 1)))))
 (let ((?x101 ((_ zero_extend 2) ?x100)))
 (let ((?x110 (bvand (bvand (_ bv63 6) (ite (= (bvand (_ bv21 6) ?x101) ?x101) (_ bv21 6) (_ bv63 6))) (ite (= (bvand (_ bv35 6) ?x101) ?x101) (_ bv35 6) (_ bv63 6)))))
 (let ((?x118 (bvand (bvand ?x110 (ite (= (bvand (_ bv26 6) ?x101) ?x101) (_ bv26 6) (_ bv63 6))) (ite (= (bvand (_ bv44 6) ?x101) ?x101) (_ bv44 6) (_ bv63 6)))))
 (= t_1_0 (bvand ?x118 (ite (= (bvand g_0 ?x101) ?x101) g_0 (_ bv63 6))))))))))
(assert
 (let ((?x98 (concat (ite signature_1_0_3 (_ bv1 1) (_ bv0 1)) (ite signature_1_0_2 (_ bv1 1) (_ bv0 1)))))
 (let ((?x100 (concat (concat ?x98 (ite signature_1_0_1 (_ bv1 1) (_ bv0 1))) (ite signature_1_0_0 (_ bv1 1) (_ bv0 1)))))
 (let ((?x101 ((_ zero_extend 2) ?x100)))
 (= (bvand t_1_0 (_ bv15 6)) ?x101)))))
(assert
 (let ((?x135 (concat (ite signature_1_1_3 (_ bv1 1) (_ bv0 1)) (ite signature_1_1_2 (_ bv1 1) (_ bv0 1)))))
 (let ((?x137 (concat (concat ?x135 (ite signature_1_1_1 (_ bv1 1) (_ bv0 1))) (ite signature_1_1_0 (_ bv1 1) (_ bv0 1)))))
 (and (distinct ?x137 (_ bv0 4)) true))))
(assert
 (let ((?x135 (concat (ite signature_1_1_3 (_ bv1 1) (_ bv0 1)) (ite signature_1_1_2 (_ bv1 1) (_ bv0 1)))))
 (let ((?x137 (concat (concat ?x135 (ite signature_1_1_1 (_ bv1 1) (_ bv0 1))) (ite signature_1_1_0 (_ bv1 1) (_ bv0 1)))))
 (let ((?x138 ((_ zero_extend 2) ?x137)))
 (let ((?x147 (bvand (bvand (_ bv63 6) (ite (= (bvand (_ bv21 6) ?x138) ?x138) (_ bv21 6) (_ bv63 6))) (ite (= (bvand (_ bv35 6) ?x138) ?x138) (_ bv35 6) (_ bv63 6)))))
 (let ((?x155 (bvand (bvand ?x147 (ite (= (bvand (_ bv26 6) ?x138) ?x138) (_ bv26 6) (_ bv63 6))) (ite (= (bvand (_ bv44 6) ?x138) ?x138) (_ bv44 6) (_ bv63 6)))))
 (let ((?x159 (bvand ?x155 (ite (= (bvand g_0 ?x138) ?x138) g_0 (_ bv63 6)))))
 (= t_1_1 ?x159))))))))
(assert
 (let ((?x135 (concat (ite signature_1_1_3 (_ bv1 1) (_ bv0 1)) (ite signature_1_1_2 (_ bv1 1) (_ bv0 1)))))
 (let ((?x137 (concat (concat ?x135 (ite signature_1_1_1 (_ bv1 1) (_ bv0 1))) (ite signature_1_1_0 (_ bv1 1) (_ bv0 1)))))
 (let ((?x138 ((_ zero_extend 2) ?x137)))
 (= (bvand t_1_1 (_ bv15 6)) ?x138)))))
(assert
 (let ((?x135 (concat (ite signature_1_1_3 (_ bv1 1) (_ bv0 1)) (ite signature_1_1_2 (_ bv1 1) (_ bv0 1)))))
 (let ((?x137 (concat (concat ?x135 (ite signature_1_1_1 (_ bv1 1) (_ bv0 1))) (ite signature_1_1_0 (_ bv1 1) (_ bv0 1)))))
 (let ((?x98 (concat (ite signature_1_0_3 (_ bv1 1) (_ bv0 1)) (ite signature_1_0_2 (_ bv1 1) (_ bv0 1)))))
 (let ((?x100 (concat (concat ?x98 (ite signature_1_0_1 (_ bv1 1) (_ bv0 1))) (ite signature_1_0_0 (_ bv1 1) (_ bv0 1)))))
 (and (distinct (bvand ?x100 (bvnot ?x137)) (_ bv0 4)) true))))))
(assert
 (let ((?x98 (concat (ite signature_1_0_3 (_ bv1 1) (_ bv0 1)) (ite signature_1_0_2 (_ bv1 1) (_ bv0 1)))))
 (let ((?x100 (concat (concat ?x98 (ite signature_1_0_1 (_ bv1 1) (_ bv0 1))) (ite signature_1_0_0 (_ bv1 1) (_ bv0 1)))))
 (let ((?x135 (concat (ite signature_1_1_3 (_ bv1 1) (_ bv0 1)) (ite signature_1_1_2 (_ bv1 1) (_ bv0 1)))))
 (let ((?x137 (concat (concat ?x135 (ite signature_1_1_1 (_ bv1 1) (_ bv0 1))) (ite signature_1_1_0 (_ bv1 1) (_ bv0 1)))))
 (and (distinct (bvand ?x137 (bvnot ?x100)) (_ bv0 4)) true))))))
(assert
 (let ((?x135 (concat (ite signature_1_1_3 (_ bv1 1) (_ bv0 1)) (ite signature_1_1_2 (_ bv1 1) (_ bv0 1)))))
 (let ((?x137 (concat (concat ?x135 (ite signature_1_1_1 (_ bv1 1) (_ bv0 1))) (ite signature_1_1_0 (_ bv1 1) (_ bv0 1)))))
 (let ((?x98 (concat (ite signature_1_0_3 (_ bv1 1) (_ bv0 1)) (ite signature_1_0_2 (_ bv1 1) (_ bv0 1)))))
 (let ((?x100 (concat (concat ?x98 (ite signature_1_0_1 (_ bv1 1) (_ bv0 1))) (ite signature_1_0_0 (_ bv1 1) (_ bv0 1)))))
 (bvult ?x100 ?x137))))))
(assert
 (= g_1 (bvor t_1_0 t_1_1)))
(assert
 (let ((?x181 (bvand (bvand (_ bv63 6) (ite (= (_ bv15 6) (bvand (_ bv21 6) (_ bv15 6))) (_ bv21 6) (_ bv63 6))) (ite (= (_ bv15 6) (bvand (_ bv35 6) (_ bv15 6))) (_ bv35 6) (_ bv63 6)))))
 (let ((?x189 (bvand (bvand ?x181 (ite (= (_ bv15 6) (bvand (_ bv26 6) (_ bv15 6))) (_ bv26 6) (_ bv63 6))) (ite (= (_ bv15 6) (bvand (_ bv44 6) (_ bv15 6))) (_ bv44 6) (_ bv63 6)))))
 (let ((?x197 (bvand (bvand ?x189 (ite (= (_ bv15 6) (bvand g_0 (_ bv15 6))) g_0 (_ bv63 6))) (ite (= (_ bv15 6) (bvand g_1 (_ bv15 6))) g_1 (_ bv63 6)))))
 (= (_ bv15 6) ?x197)))))
(assert
 (let (($x200 (= ((_ extract 4 4) g_0) (_ bv0 1))))
 ((_ at-least 1) $x200 (= ((_ extract 4 4) g_1) (_ bv0 1)))))
(assert
 (let (($x205 (= ((_ extract 5 5) g_0) (_ bv0 1))))
 ((_ at-least 1) $x205 (= ((_ extract 5 5) g_1) (_ bv0 1)))))
(assert
 (=> cover_1_0_1 (= ((_ extract 4 4) (_ bv35 6)) (_ bv0 1))))
(assert
 (=> cover_1_0_3 (= ((_ extract 4 4) (_ bv44 6)) (_ bv0 1))))
(assert
 (let (($x200 (= ((_ extract 4 4) g_0) (_ bv0 1))))
 (=> cover_1_0_4 $x200)))
(assert
 (or (and cover_1_0_1 (= ((_ extract 0 0) (_ bv35 6)) (_ bv1 1))) (and cover_1_0_3 (= ((_ extract 0 0) (_ bv44 6)) (_ bv1 1))) (and cover_1_0_4 (= ((_ extract 0 0) g_0) (_ bv1 1)))))
(assert
 (or (and cover_1_0_1 (= ((_ extract 1 1) (_ bv35 6)) (_ bv1 1))) (and cover_1_0_3 (= ((_ extract 1 1) (_ bv44 6)) (_ bv1 1))) (and cover_1_0_4 (= ((_ extract 1 1) g_0) (_ bv1 1)))))
(assert
 (or (and cover_1_0_1 (= ((_ extract 2 2) (_ bv35 6)) (_ bv1 1))) (and cover_1_0_3 (= ((_ extract 2 2) (_ bv44 6)) (_ bv1 1))) (and cover_1_0_4 (= ((_ extract 2 2) g_0) (_ bv1 1)))))
(assert
 (or (and cover_1_0_1 (= ((_ extract 3 3) (_ bv35 6)) (_ bv1 1))) (and cover_1_0_3 (= ((_ extract 3 3) (_ bv44 6)) (_ bv1 1))) (and cover_1_0_4 (= ((_ extract 3 3) g_0) (_ bv1 1)))))
(assert
 ((_ at-most 2) cover_1_0_1 cover_1_0_3 cover_1_0_4 (= ((_ extract 4 4) g_1) (_ bv1 1))))
(assert
 (=> cover_1_1_0 (= ((_ extract 5 5) (_ bv21 6)) (_ bv0 1))))
(assert
 (=> cover_1_1_2 (= ((_ extract 5 5) (_ bv26 6)) (_ bv0 1))))
(assert
 (let (($x205 (= ((_ extract 5 5) g_0) (_ bv0 1))))
 (=> cover_1_1_4 $x205)))
(assert
 (or (and cover_1_1_0 (= ((_ extract 0 0) (_ bv21 6)) (_ bv1 1))) (and cover_1_1_2 (= ((_ extract 0 0) (_ bv26 6)) (_ bv1 1))) (and cover_1_1_4 (= ((_ extract 0 0) g_0) (_ bv1 1)))))
(assert
 (or (and cover_1_1_0 (= ((_ extract 1 1) (_ bv21 6)) (_ bv1 1))) (and cover_1_1_2 (= ((_ extract 1 1) (_ bv26 6)) (_ bv1 1))) (and cover_1_1_4 (= ((_ extract 1 1) g_0) (_ bv1 1)))))
(assert
 (or (and cover_1_1_0 (= ((_ extract 2 2) (_ bv21 6)) (_ bv1 1))) (and cover_1_1_2 (= ((_ extract 2 2) (_ bv26 6)) (_ bv1 1))) (and cover_1_1_4 (= ((_ extract 2 2) g_0) (_ bv1 1)))))
(assert
 (or (and cover_1_1_0 (= ((_ extract 3 3) (_ bv21 6)) (_ bv1 1))) (and cover_1_1_2 (= ((_ extract 3 3) (_ bv26 6)) (_ bv1 1))) (and cover_1_1_4 (= ((_ extract 3 3) g_0) (_ bv1 1)))))
(assert
 (let ((?x206 ((_ extract 5 5) g_1)))
(let (($x303 (= ?x206 (_ bv1 1))))
((_ at-most 2) cover_1_1_0 cover_1_1_2 cover_1_1_4 $x303))))
(check-sat)
