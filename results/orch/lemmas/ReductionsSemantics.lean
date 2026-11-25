import ReductionsIR

namespace PEqualNP.Outside.Pilot64Bridge

set_option maxRecDepth 100000
set_option maxHeartbeats 0

@[simp] theorem select_false_4 : ∀ (i : Fin 4),
    ([false, false, false, false] : List Bool).getD i.val false = false := by decide
@[simp] theorem index_false_4 : ∀ (i : Fin 4),
    ([false, false, false, false] : List Bool)[i.val]'(by exact i.isLt) = false := by decide
@[simp] theorem select_true_4 : ∀ (i : Fin 4),
    ([true, true, true, true] : List Bool).getD i.val false = true := by decide
@[simp] theorem index_true_4 : ∀ (i : Fin 4),
    ([true, true, true, true] : List Bool)[i.val]'(by exact i.isLt) = true := by decide
@[simp] theorem select_false_5 : ∀ (i : Fin 5),
    ([false, false, false, false, false] : List Bool).getD i.val false = false := by decide
@[simp] theorem index_false_5 : ∀ (i : Fin 5),
    ([false, false, false, false, false] : List Bool)[i.val]'(by exact i.isLt) = false := by decide
@[simp] theorem select_true_5 : ∀ (i : Fin 5),
    ([true, true, true, true, true] : List Bool).getD i.val false = true := by decide
@[simp] theorem index_true_5 : ∀ (i : Fin 5),
    ([true, true, true, true, true] : List Bool)[i.val]'(by exact i.isLt) = true := by decide
@[simp] theorem select_false_6 : ∀ (i : Fin 6),
    ([false, false, false, false, false, false] : List Bool).getD i.val false = false := by decide
@[simp] theorem index_false_6 : ∀ (i : Fin 6),
    ([false, false, false, false, false, false] : List Bool)[i.val]'(by exact i.isLt) = false := by decide
@[simp] theorem select_true_6 : ∀ (i : Fin 6),
    ([true, true, true, true, true, true] : List Bool).getD i.val false = true := by decide
@[simp] theorem index_true_6 : ∀ (i : Fin 6),
    ([true, true, true, true, true, true] : List Bool)[i.val]'(by exact i.isLt) = true := by decide
@[simp] theorem select_false_7 : ∀ (i : Fin 7),
    ([false, false, false, false, false, false, false] : List Bool).getD i.val false = false := by decide
@[simp] theorem index_false_7 : ∀ (i : Fin 7),
    ([false, false, false, false, false, false, false] : List Bool)[i.val]'(by exact i.isLt) = false := by decide
@[simp] theorem select_true_7 : ∀ (i : Fin 7),
    ([true, true, true, true, true, true, true] : List Bool).getD i.val false = true := by decide
@[simp] theorem index_true_7 : ∀ (i : Fin 7),
    ([true, true, true, true, true, true, true] : List Bool)[i.val]'(by exact i.isLt) = true := by decide
@[simp] theorem select_false_8 : ∀ (i : Fin 8),
    ([false, false, false, false, false, false, false, false] : List Bool).getD i.val false = false := by decide
@[simp] theorem index_false_8 : ∀ (i : Fin 8),
    ([false, false, false, false, false, false, false, false] : List Bool)[i.val]'(by exact i.isLt) = false := by decide
@[simp] theorem select_true_8 : ∀ (i : Fin 8),
    ([true, true, true, true, true, true, true, true] : List Bool).getD i.val false = true := by decide
@[simp] theorem index_true_8 : ∀ (i : Fin 8),
    ([true, true, true, true, true, true, true, true] : List Bool)[i.val]'(by exact i.isLt) = true := by decide
@[simp] theorem mask_bit_0_0 : (0 : Nat).testBit 0 = false := by decide
@[simp] theorem mask_bit_0_1 : (0 : Nat).testBit 1 = false := by decide
@[simp] theorem mask_bit_0_2 : (0 : Nat).testBit 2 = false := by decide
@[simp] theorem mask_bit_0_3 : (0 : Nat).testBit 3 = false := by decide
@[simp] theorem mask_bit_1_0 : (1 : Nat).testBit 0 = true := by decide
@[simp] theorem mask_bit_1_1 : (1 : Nat).testBit 1 = false := by decide
@[simp] theorem mask_bit_1_2 : (1 : Nat).testBit 2 = false := by decide
@[simp] theorem mask_bit_1_3 : (1 : Nat).testBit 3 = false := by decide
@[simp] theorem mask_bit_2_0 : (2 : Nat).testBit 0 = false := by decide
@[simp] theorem mask_bit_2_1 : (2 : Nat).testBit 1 = true := by decide
@[simp] theorem mask_bit_2_2 : (2 : Nat).testBit 2 = false := by decide
@[simp] theorem mask_bit_2_3 : (2 : Nat).testBit 3 = false := by decide
@[simp] theorem mask_bit_3_0 : (3 : Nat).testBit 0 = true := by decide
@[simp] theorem mask_bit_3_1 : (3 : Nat).testBit 1 = true := by decide
@[simp] theorem mask_bit_3_2 : (3 : Nat).testBit 2 = false := by decide
@[simp] theorem mask_bit_3_3 : (3 : Nat).testBit 3 = false := by decide
@[simp] theorem mask_bit_4_0 : (4 : Nat).testBit 0 = false := by decide
@[simp] theorem mask_bit_4_1 : (4 : Nat).testBit 1 = false := by decide
@[simp] theorem mask_bit_4_2 : (4 : Nat).testBit 2 = true := by decide
@[simp] theorem mask_bit_4_3 : (4 : Nat).testBit 3 = false := by decide
@[simp] theorem mask_bit_5_0 : (5 : Nat).testBit 0 = true := by decide
@[simp] theorem mask_bit_5_1 : (5 : Nat).testBit 1 = false := by decide
@[simp] theorem mask_bit_5_2 : (5 : Nat).testBit 2 = true := by decide
@[simp] theorem mask_bit_5_3 : (5 : Nat).testBit 3 = false := by decide
@[simp] theorem mask_bit_6_0 : (6 : Nat).testBit 0 = false := by decide
@[simp] theorem mask_bit_6_1 : (6 : Nat).testBit 1 = true := by decide
@[simp] theorem mask_bit_6_2 : (6 : Nat).testBit 2 = true := by decide
@[simp] theorem mask_bit_6_3 : (6 : Nat).testBit 3 = false := by decide
@[simp] theorem mask_bit_7_0 : (7 : Nat).testBit 0 = true := by decide
@[simp] theorem mask_bit_7_1 : (7 : Nat).testBit 1 = true := by decide
@[simp] theorem mask_bit_7_2 : (7 : Nat).testBit 2 = true := by decide
@[simp] theorem mask_bit_7_3 : (7 : Nat).testBit 3 = false := by decide
@[simp] theorem mask_bit_8_0 : (8 : Nat).testBit 0 = false := by decide
@[simp] theorem mask_bit_8_1 : (8 : Nat).testBit 1 = false := by decide
@[simp] theorem mask_bit_8_2 : (8 : Nat).testBit 2 = false := by decide
@[simp] theorem mask_bit_8_3 : (8 : Nat).testBit 3 = true := by decide
@[simp] theorem mask_bit_9_0 : (9 : Nat).testBit 0 = true := by decide
@[simp] theorem mask_bit_9_1 : (9 : Nat).testBit 1 = false := by decide
@[simp] theorem mask_bit_9_2 : (9 : Nat).testBit 2 = false := by decide
@[simp] theorem mask_bit_9_3 : (9 : Nat).testBit 3 = true := by decide
@[simp] theorem mask_bit_10_0 : (10 : Nat).testBit 0 = false := by decide
@[simp] theorem mask_bit_10_1 : (10 : Nat).testBit 1 = true := by decide
@[simp] theorem mask_bit_10_2 : (10 : Nat).testBit 2 = false := by decide
@[simp] theorem mask_bit_10_3 : (10 : Nat).testBit 3 = true := by decide
@[simp] theorem mask_bit_11_0 : (11 : Nat).testBit 0 = true := by decide
@[simp] theorem mask_bit_11_1 : (11 : Nat).testBit 1 = true := by decide
@[simp] theorem mask_bit_11_2 : (11 : Nat).testBit 2 = false := by decide
@[simp] theorem mask_bit_11_3 : (11 : Nat).testBit 3 = true := by decide
@[simp] theorem mask_bit_12_0 : (12 : Nat).testBit 0 = false := by decide
@[simp] theorem mask_bit_12_1 : (12 : Nat).testBit 1 = false := by decide
@[simp] theorem mask_bit_12_2 : (12 : Nat).testBit 2 = true := by decide
@[simp] theorem mask_bit_12_3 : (12 : Nat).testBit 3 = true := by decide
@[simp] theorem mask_bit_13_0 : (13 : Nat).testBit 0 = true := by decide
@[simp] theorem mask_bit_13_1 : (13 : Nat).testBit 1 = false := by decide
@[simp] theorem mask_bit_13_2 : (13 : Nat).testBit 2 = true := by decide
@[simp] theorem mask_bit_13_3 : (13 : Nat).testBit 3 = true := by decide
@[simp] theorem mask_bit_14_0 : (14 : Nat).testBit 0 = false := by decide
@[simp] theorem mask_bit_14_1 : (14 : Nat).testBit 1 = true := by decide
@[simp] theorem mask_bit_14_2 : (14 : Nat).testBit 2 = true := by decide
@[simp] theorem mask_bit_14_3 : (14 : Nat).testBit 3 = true := by decide
@[simp] theorem mask_bit_15_0 : (15 : Nat).testBit 0 = true := by decide
@[simp] theorem mask_bit_15_1 : (15 : Nat).testBit 1 = true := by decide
@[simp] theorem mask_bit_15_2 : (15 : Nat).testBit 2 = true := by decide
@[simp] theorem mask_bit_15_3 : (15 : Nat).testBit 3 = true := by decide

def evalCircuit (c : Candidate) (mask : Nat) : List Bool :=
  let w0 := [mask.testBit 0, mask.testBit 1, mask.testBit 2, mask.testBit 3]
  let w1 := w0 ++ [if c.op0 then (w0.getD c.a0.val false) && (w0.getD c.b0.val false) else (w0.getD c.a0.val false) || (w0.getD c.b0.val false)]
  let w2 := w1 ++ [if c.op1 then (w1.getD c.a1.val false) && (w1.getD c.b1.val false) else (w1.getD c.a1.val false) || (w1.getD c.b1.val false)]
  let w3 := w2 ++ [if c.op2 then (w2.getD c.a2.val false) && (w2.getD c.b2.val false) else (w2.getD c.a2.val false) || (w2.getD c.b2.val false)]
  let w4 := w3 ++ [if c.op3 then (w3.getD c.a3.val false) && (w3.getD c.b3.val false) else (w3.getD c.a3.val false) || (w3.getD c.b3.val false)]
  let w5 := w4 ++ [if c.op4 then (w4.getD c.a4.val false) && (w4.getD c.b4.val false) else (w4.getD c.a4.val false) || (w4.getD c.b4.val false)]
  w5

def derivativeCircuit (c : Candidate) (base seed : Nat) : List Bool :=
  let v0 := [(1 <<< base).testBit 0, (1 <<< base).testBit 1, (1 <<< base).testBit 2, (1 <<< base).testBit 3]
  let d0 := [decide (seed = 0), decide (seed = 1), decide (seed = 2), decide (seed = 3)]
  let d1 := d0 ++ [if c.op0 then ((v0.getD c.a0.val false) && (d0.getD c.b0.val false)) || ((d0.getD c.a0.val false) && (v0.getD c.b0.val false)) else (d0.getD c.a0.val false) || (d0.getD c.b0.val false)]
  let v1 := v0 ++ [if c.op0 then (v0.getD c.a0.val false) && (v0.getD c.b0.val false) else (v0.getD c.a0.val false) || (v0.getD c.b0.val false)]
  let d2 := d1 ++ [if c.op1 then ((v1.getD c.a1.val false) && (d1.getD c.b1.val false)) || ((d1.getD c.a1.val false) && (v1.getD c.b1.val false)) else (d1.getD c.a1.val false) || (d1.getD c.b1.val false)]
  let v2 := v1 ++ [if c.op1 then (v1.getD c.a1.val false) && (v1.getD c.b1.val false) else (v1.getD c.a1.val false) || (v1.getD c.b1.val false)]
  let d3 := d2 ++ [if c.op2 then ((v2.getD c.a2.val false) && (d2.getD c.b2.val false)) || ((d2.getD c.a2.val false) && (v2.getD c.b2.val false)) else (d2.getD c.a2.val false) || (d2.getD c.b2.val false)]
  let v3 := v2 ++ [if c.op2 then (v2.getD c.a2.val false) && (v2.getD c.b2.val false) else (v2.getD c.a2.val false) || (v2.getD c.b2.val false)]
  let d4 := d3 ++ [if c.op3 then ((v3.getD c.a3.val false) && (d3.getD c.b3.val false)) || ((d3.getD c.a3.val false) && (v3.getD c.b3.val false)) else (d3.getD c.a3.val false) || (d3.getD c.b3.val false)]
  let v4 := v3 ++ [if c.op3 then (v3.getD c.a3.val false) && (v3.getD c.b3.val false) else (v3.getD c.a3.val false) || (v3.getD c.b3.val false)]
  let d5 := d4 ++ [if c.op4 then ((v4.getD c.a4.val false) && (d4.getD c.b4.val false)) || ((d4.getD c.a4.val false) && (v4.getD c.b4.val false)) else (d4.getD c.a4.val false) || (d4.getD c.b4.val false)]
  let v5 := v4 ++ [if c.op4 then (v4.getD c.a4.val false) && (v4.getD c.b4.val false) else (v4.getD c.a4.val false) || (v4.getD c.b4.val false)]
  d5

theorem output_eq_evalCircuit (c : Candidate) (r : Fin 16) :
    output c r = (evalCircuit c r.val).getD 8 false := by
  rcases r with ⟨r, hr⟩
  have h : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9 ∨ r = 10 ∨ r = 11 ∨ r = 12 ∨ r = 13 ∨ r = 14 ∨ r = 15 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change (v129 c) = (evalCircuit c 0).getD 8 false
    simp [evalCircuit, v2, v17, v36, v59, v86, v117, v118, v119, v120, v121, v122, v123, v124, v125, v126, v127, v128, v129]
  · change (v144 c) = (evalCircuit c 1).getD 8 false
    simp [evalCircuit, v2, v17, v36, v59, v86, v130, v131, v132, v133, v134, v135, v136, v137, v138, v139, v140, v141, v142, v143, v144]
  · change (v159 c) = (evalCircuit c 2).getD 8 false
    simp [evalCircuit, v2, v17, v36, v59, v86, v145, v146, v147, v148, v149, v150, v151, v152, v153, v154, v155, v156, v157, v158, v159]
  · change (v174 c) = (evalCircuit c 3).getD 8 false
    simp [evalCircuit, v2, v17, v36, v59, v86, v160, v161, v162, v163, v164, v165, v166, v167, v168, v169, v170, v171, v172, v173, v174]
  · change (v189 c) = (evalCircuit c 4).getD 8 false
    simp [evalCircuit, v2, v17, v36, v59, v86, v175, v176, v177, v178, v179, v180, v181, v182, v183, v184, v185, v186, v187, v188, v189]
  · change (v204 c) = (evalCircuit c 5).getD 8 false
    simp [evalCircuit, v2, v17, v36, v59, v86, v190, v191, v192, v193, v194, v195, v196, v197, v198, v199, v200, v201, v202, v203, v204]
  · change (v219 c) = (evalCircuit c 6).getD 8 false
    simp [evalCircuit, v2, v17, v36, v59, v86, v205, v206, v207, v208, v209, v210, v211, v212, v213, v214, v215, v216, v217, v218, v219]
  · change (v234 c) = (evalCircuit c 7).getD 8 false
    simp [evalCircuit, v2, v17, v36, v59, v86, v220, v221, v222, v223, v224, v225, v226, v227, v228, v229, v230, v231, v232, v233, v234]
  · change (v249 c) = (evalCircuit c 8).getD 8 false
    simp [evalCircuit, v2, v17, v36, v59, v86, v235, v236, v237, v238, v239, v240, v241, v242, v243, v244, v245, v246, v247, v248, v249]
  · change (v264 c) = (evalCircuit c 9).getD 8 false
    simp [evalCircuit, v2, v17, v36, v59, v86, v250, v251, v252, v253, v254, v255, v256, v257, v258, v259, v260, v261, v262, v263, v264]
  · change (v279 c) = (evalCircuit c 10).getD 8 false
    simp [evalCircuit, v2, v17, v36, v59, v86, v265, v266, v267, v268, v269, v270, v271, v272, v273, v274, v275, v276, v277, v278, v279]
  · change (v294 c) = (evalCircuit c 11).getD 8 false
    simp [evalCircuit, v2, v17, v36, v59, v86, v280, v281, v282, v283, v284, v285, v286, v287, v288, v289, v290, v291, v292, v293, v294]
  · change (v309 c) = (evalCircuit c 12).getD 8 false
    simp [evalCircuit, v2, v17, v36, v59, v86, v295, v296, v297, v298, v299, v300, v301, v302, v303, v304, v305, v306, v307, v308, v309]
  · change (v324 c) = (evalCircuit c 13).getD 8 false
    simp [evalCircuit, v2, v17, v36, v59, v86, v310, v311, v312, v313, v314, v315, v316, v317, v318, v319, v320, v321, v322, v323, v324]
  · change (v339 c) = (evalCircuit c 14).getD 8 false
    simp [evalCircuit, v2, v17, v36, v59, v86, v325, v326, v327, v328, v329, v330, v331, v332, v333, v334, v335, v336, v337, v338, v339]
  · change (v352 c) = (evalCircuit c 15).getD 8 false
    simp [evalCircuit, v2, v17, v36, v59, v86, v340, v341, v342, v343, v344, v345, v346, v347, v348, v349, v350, v351, v352]

theorem derivativeLeft_eq (c : Candidate) :
    derivativeLeft c = (derivativeCircuit c 0 1).getD 8 false := by
  change (v402 c) = (derivativeCircuit c 0 1).getD 8 false
  simp [derivativeCircuit, v2, v17, v36, v59, v86, v353, v354, v355, v356, v357, v358, v359, v360, v361, v362, v363, v364, v365, v366, v368, v369, v370, v371, v372, v373, v374, v375, v376, v377, v378, v379, v380, v381, v382, v383, v384, v385, v386, v387, v388, v389, v390, v391, v392, v393, v394, v395, v396, v397, v398, v399, v400, v401, v402]

theorem derivativeRight_eq (c : Candidate) :
    derivativeRight c = (derivativeCircuit c 1 0).getD 8 false := by
  change (v452 c) = (derivativeCircuit c 1 0).getD 8 false
  simp [derivativeCircuit, v2, v17, v36, v59, v86, v403, v404, v405, v406, v407, v408, v409, v410, v411, v412, v413, v414, v415, v416, v418, v419, v420, v421, v422, v423, v424, v425, v426, v427, v428, v429, v430, v431, v432, v433, v434, v435, v436, v437, v438, v439, v440, v441, v442, v443, v444, v445, v446, v447, v448, v449, v450, v451, v452]

end PEqualNP.Outside.Pilot64Bridge
