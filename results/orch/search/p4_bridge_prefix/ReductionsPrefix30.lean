import Reductions

namespace PEqualNP.Outside.Pilot64Bridge

open PEqualNP.Library.LRAT
open PEqualNP.Outside.Pilot64KernelControl

set_option maxRecDepth 100000
set_option maxHeartbeats 0

structure Candidate where
  op0 : Bool
  a0 : Fin 4
  b0 : Fin 4
  op1 : Bool
  a1 : Fin 5
  b1 : Fin 5
  op2 : Bool
  a2 : Fin 6
  b2 : Fin 6
  op3 : Bool
  a3 : Fin 7
  b3 : Fin 7
  op4 : Bool
  a4 : Fin 8
  b4 : Fin 8

def valid (c : Candidate) : Prop :=
  c.a0.val < c.b0.val ∧ c.a1.val < c.b1.val ∧ c.a2.val < c.b2.val ∧ c.a3.val < c.b3.val ∧ c.a4.val < c.b4.val

def v2 (c : Candidate) : Bool := c.op0
def v3 (c : Candidate) : Bool := decide (c.a0.val = 0)
def v4 (c : Candidate) : Bool := decide (c.a0.val = 1)
def v5 (c : Candidate) : Bool := decide (c.a0.val = 2)
def v6 (c : Candidate) : Bool := decide (c.a0.val = 3)
def v7 (c : Candidate) : Bool := decide (c.b0.val = 0)
def v8 (c : Candidate) : Bool := decide (c.b0.val = 1)
def v9 (c : Candidate) : Bool := decide (c.b0.val = 2)
def v10 (c : Candidate) : Bool := decide (c.b0.val = 3)
def v11 (c : Candidate) : Bool := !(v3 c) && !(v4 c)
def v12 (c : Candidate) : Bool := (v11 c) && !(v5 c)
def v13 (c : Candidate) : Bool := (v12 c) && !(v6 c)
def v14 (c : Candidate) : Bool := !(v7 c) && !(v8 c)
def v15 (c : Candidate) : Bool := (v14 c) && !(v9 c)
def v16 (c : Candidate) : Bool := (v15 c) && !(v10 c)
def v17 (c : Candidate) : Bool := c.op1
def v18 (c : Candidate) : Bool := decide (c.a1.val = 0)
def v19 (c : Candidate) : Bool := decide (c.a1.val = 1)
def v20 (c : Candidate) : Bool := decide (c.a1.val = 2)
def v21 (c : Candidate) : Bool := decide (c.a1.val = 3)
def v22 (c : Candidate) : Bool := decide (c.a1.val = 4)
def v23 (c : Candidate) : Bool := decide (c.b1.val = 0)
def v24 (c : Candidate) : Bool := decide (c.b1.val = 1)
def v25 (c : Candidate) : Bool := decide (c.b1.val = 2)
def v26 (c : Candidate) : Bool := decide (c.b1.val = 3)
def v27 (c : Candidate) : Bool := decide (c.b1.val = 4)
def v28 (c : Candidate) : Bool := !(v18 c) && !(v19 c)
def v29 (c : Candidate) : Bool := (v28 c) && !(v20 c)
def v30 (c : Candidate) : Bool := (v29 c) && !(v21 c)
def v31 (c : Candidate) : Bool := (v30 c) && !(v22 c)
def v32 (c : Candidate) : Bool := !(v23 c) && !(v24 c)
def v33 (c : Candidate) : Bool := (v32 c) && !(v25 c)
def v34 (c : Candidate) : Bool := (v33 c) && !(v26 c)
def v35 (c : Candidate) : Bool := (v34 c) && !(v27 c)
def v36 (c : Candidate) : Bool := c.op2
def v37 (c : Candidate) : Bool := decide (c.a2.val = 0)
def v38 (c : Candidate) : Bool := decide (c.a2.val = 1)
def v39 (c : Candidate) : Bool := decide (c.a2.val = 2)
def v40 (c : Candidate) : Bool := decide (c.a2.val = 3)
def v41 (c : Candidate) : Bool := decide (c.a2.val = 4)
def v42 (c : Candidate) : Bool := decide (c.a2.val = 5)
def v43 (c : Candidate) : Bool := decide (c.b2.val = 0)
def v44 (c : Candidate) : Bool := decide (c.b2.val = 1)
def v45 (c : Candidate) : Bool := decide (c.b2.val = 2)
def v46 (c : Candidate) : Bool := decide (c.b2.val = 3)
def v47 (c : Candidate) : Bool := decide (c.b2.val = 4)
def v48 (c : Candidate) : Bool := decide (c.b2.val = 5)
def v49 (c : Candidate) : Bool := !(v37 c) && !(v38 c)
def v50 (c : Candidate) : Bool := (v49 c) && !(v39 c)
def v51 (c : Candidate) : Bool := (v50 c) && !(v40 c)
def v52 (c : Candidate) : Bool := (v51 c) && !(v41 c)
def v53 (c : Candidate) : Bool := (v52 c) && !(v42 c)
def v54 (c : Candidate) : Bool := !(v43 c) && !(v44 c)
def v55 (c : Candidate) : Bool := (v54 c) && !(v45 c)
def v56 (c : Candidate) : Bool := (v55 c) && !(v46 c)
def v57 (c : Candidate) : Bool := (v56 c) && !(v47 c)
def v58 (c : Candidate) : Bool := (v57 c) && !(v48 c)
def v59 (c : Candidate) : Bool := c.op3
def v60 (c : Candidate) : Bool := decide (c.a3.val = 0)
def v61 (c : Candidate) : Bool := decide (c.a3.val = 1)
def v62 (c : Candidate) : Bool := decide (c.a3.val = 2)
def v63 (c : Candidate) : Bool := decide (c.a3.val = 3)
def v64 (c : Candidate) : Bool := decide (c.a3.val = 4)
def v65 (c : Candidate) : Bool := decide (c.a3.val = 5)
def v66 (c : Candidate) : Bool := decide (c.a3.val = 6)
def v67 (c : Candidate) : Bool := decide (c.b3.val = 0)
def v68 (c : Candidate) : Bool := decide (c.b3.val = 1)
def v69 (c : Candidate) : Bool := decide (c.b3.val = 2)
def v70 (c : Candidate) : Bool := decide (c.b3.val = 3)
def v71 (c : Candidate) : Bool := decide (c.b3.val = 4)
def v72 (c : Candidate) : Bool := decide (c.b3.val = 5)
def v73 (c : Candidate) : Bool := decide (c.b3.val = 6)
def v74 (c : Candidate) : Bool := !(v60 c) && !(v61 c)
def v75 (c : Candidate) : Bool := (v74 c) && !(v62 c)
def v76 (c : Candidate) : Bool := (v75 c) && !(v63 c)
def v77 (c : Candidate) : Bool := (v76 c) && !(v64 c)
def v78 (c : Candidate) : Bool := (v77 c) && !(v65 c)
def v79 (c : Candidate) : Bool := (v78 c) && !(v66 c)
def v80 (c : Candidate) : Bool := !(v67 c) && !(v68 c)
def v81 (c : Candidate) : Bool := (v80 c) && !(v69 c)
def v82 (c : Candidate) : Bool := (v81 c) && !(v70 c)
def v83 (c : Candidate) : Bool := (v82 c) && !(v71 c)
def v84 (c : Candidate) : Bool := (v83 c) && !(v72 c)
def v85 (c : Candidate) : Bool := (v84 c) && !(v73 c)
def v86 (c : Candidate) : Bool := c.op4
def v87 (c : Candidate) : Bool := decide (c.a4.val = 0)
def v88 (c : Candidate) : Bool := decide (c.a4.val = 1)
def v89 (c : Candidate) : Bool := decide (c.a4.val = 2)
def v90 (c : Candidate) : Bool := decide (c.a4.val = 3)
def v91 (c : Candidate) : Bool := decide (c.a4.val = 4)
def v92 (c : Candidate) : Bool := decide (c.a4.val = 5)
def v93 (c : Candidate) : Bool := decide (c.a4.val = 6)
def v94 (c : Candidate) : Bool := decide (c.a4.val = 7)
def v95 (c : Candidate) : Bool := decide (c.b4.val = 0)
def v96 (c : Candidate) : Bool := decide (c.b4.val = 1)
def v97 (c : Candidate) : Bool := decide (c.b4.val = 2)
def v98 (c : Candidate) : Bool := decide (c.b4.val = 3)
def v99 (c : Candidate) : Bool := decide (c.b4.val = 4)
def v100 (c : Candidate) : Bool := decide (c.b4.val = 5)
def v101 (c : Candidate) : Bool := decide (c.b4.val = 6)
def v102 (c : Candidate) : Bool := decide (c.b4.val = 7)
def v103 (c : Candidate) : Bool := !(v87 c) && !(v88 c)
def v104 (c : Candidate) : Bool := (v103 c) && !(v89 c)
def v105 (c : Candidate) : Bool := (v104 c) && !(v90 c)
def v106 (c : Candidate) : Bool := (v105 c) && !(v91 c)
def v107 (c : Candidate) : Bool := (v106 c) && !(v92 c)
def v108 (c : Candidate) : Bool := (v107 c) && !(v93 c)
def v109 (c : Candidate) : Bool := (v108 c) && !(v94 c)
def v110 (c : Candidate) : Bool := !(v95 c) && !(v96 c)
def v111 (c : Candidate) : Bool := (v110 c) && !(v97 c)
def v112 (c : Candidate) : Bool := (v111 c) && !(v98 c)
def v113 (c : Candidate) : Bool := (v112 c) && !(v99 c)
def v114 (c : Candidate) : Bool := (v113 c) && !(v100 c)
def v115 (c : Candidate) : Bool := (v114 c) && !(v101 c)
def v116 (c : Candidate) : Bool := (v115 c) && !(v102 c)
def v117 (c : Candidate) : Bool := if (v2 c) then false && false else false || false
def v118 (c : Candidate) : Bool := ([false, false, false, false, (v117 c)] : List Bool).getD c.a1.val false
def v119 (c : Candidate) : Bool := ([false, false, false, false, (v117 c)] : List Bool).getD c.b1.val false
def v120 (c : Candidate) : Bool := if (v17 c) then (v118 c) && (v119 c) else (v118 c) || (v119 c)
def v121 (c : Candidate) : Bool := ([false, false, false, false, (v117 c), (v120 c)] : List Bool).getD c.a2.val false
def v122 (c : Candidate) : Bool := ([false, false, false, false, (v117 c), (v120 c)] : List Bool).getD c.b2.val false
def v123 (c : Candidate) : Bool := if (v36 c) then (v121 c) && (v122 c) else (v121 c) || (v122 c)
def v124 (c : Candidate) : Bool := ([false, false, false, false, (v117 c), (v120 c), (v123 c)] : List Bool).getD c.a3.val false
def v125 (c : Candidate) : Bool := ([false, false, false, false, (v117 c), (v120 c), (v123 c)] : List Bool).getD c.b3.val false
def v126 (c : Candidate) : Bool := if (v59 c) then (v124 c) && (v125 c) else (v124 c) || (v125 c)
def v127 (c : Candidate) : Bool := ([false, false, false, false, (v117 c), (v120 c), (v123 c), (v126 c)] : List Bool).getD c.a4.val false
def v128 (c : Candidate) : Bool := ([false, false, false, false, (v117 c), (v120 c), (v123 c), (v126 c)] : List Bool).getD c.b4.val false
def v129 (c : Candidate) : Bool := if (v86 c) then (v127 c) && (v128 c) else (v127 c) || (v128 c)
def v130 (c : Candidate) : Bool := ([true, false, false, false] : List Bool).getD c.a0.val false
def v131 (c : Candidate) : Bool := ([true, false, false, false] : List Bool).getD c.b0.val false
def v132 (c : Candidate) : Bool := if (v2 c) then (v130 c) && (v131 c) else (v130 c) || (v131 c)
def v133 (c : Candidate) : Bool := ([true, false, false, false, (v132 c)] : List Bool).getD c.a1.val false
def v134 (c : Candidate) : Bool := ([true, false, false, false, (v132 c)] : List Bool).getD c.b1.val false
def v135 (c : Candidate) : Bool := if (v17 c) then (v133 c) && (v134 c) else (v133 c) || (v134 c)
def v136 (c : Candidate) : Bool := ([true, false, false, false, (v132 c), (v135 c)] : List Bool).getD c.a2.val false
def v137 (c : Candidate) : Bool := ([true, false, false, false, (v132 c), (v135 c)] : List Bool).getD c.b2.val false
def v138 (c : Candidate) : Bool := if (v36 c) then (v136 c) && (v137 c) else (v136 c) || (v137 c)
def v139 (c : Candidate) : Bool := ([true, false, false, false, (v132 c), (v135 c), (v138 c)] : List Bool).getD c.a3.val false
def v140 (c : Candidate) : Bool := ([true, false, false, false, (v132 c), (v135 c), (v138 c)] : List Bool).getD c.b3.val false
def v141 (c : Candidate) : Bool := if (v59 c) then (v139 c) && (v140 c) else (v139 c) || (v140 c)
def v142 (c : Candidate) : Bool := ([true, false, false, false, (v132 c), (v135 c), (v138 c), (v141 c)] : List Bool).getD c.a4.val false
def v143 (c : Candidate) : Bool := ([true, false, false, false, (v132 c), (v135 c), (v138 c), (v141 c)] : List Bool).getD c.b4.val false
def v144 (c : Candidate) : Bool := if (v86 c) then (v142 c) && (v143 c) else (v142 c) || (v143 c)
def v145 (c : Candidate) : Bool := ([false, true, false, false] : List Bool).getD c.a0.val false
def v146 (c : Candidate) : Bool := ([false, true, false, false] : List Bool).getD c.b0.val false
def v147 (c : Candidate) : Bool := if (v2 c) then (v145 c) && (v146 c) else (v145 c) || (v146 c)
def v148 (c : Candidate) : Bool := ([false, true, false, false, (v147 c)] : List Bool).getD c.a1.val false
def v149 (c : Candidate) : Bool := ([false, true, false, false, (v147 c)] : List Bool).getD c.b1.val false
def v150 (c : Candidate) : Bool := if (v17 c) then (v148 c) && (v149 c) else (v148 c) || (v149 c)
def v151 (c : Candidate) : Bool := ([false, true, false, false, (v147 c), (v150 c)] : List Bool).getD c.a2.val false
def v152 (c : Candidate) : Bool := ([false, true, false, false, (v147 c), (v150 c)] : List Bool).getD c.b2.val false
def v153 (c : Candidate) : Bool := if (v36 c) then (v151 c) && (v152 c) else (v151 c) || (v152 c)
def v154 (c : Candidate) : Bool := ([false, true, false, false, (v147 c), (v150 c), (v153 c)] : List Bool).getD c.a3.val false
def v155 (c : Candidate) : Bool := ([false, true, false, false, (v147 c), (v150 c), (v153 c)] : List Bool).getD c.b3.val false
def v156 (c : Candidate) : Bool := if (v59 c) then (v154 c) && (v155 c) else (v154 c) || (v155 c)
def v157 (c : Candidate) : Bool := ([false, true, false, false, (v147 c), (v150 c), (v153 c), (v156 c)] : List Bool).getD c.a4.val false
def v158 (c : Candidate) : Bool := ([false, true, false, false, (v147 c), (v150 c), (v153 c), (v156 c)] : List Bool).getD c.b4.val false
def v159 (c : Candidate) : Bool := if (v86 c) then (v157 c) && (v158 c) else (v157 c) || (v158 c)
def v160 (c : Candidate) : Bool := ([true, true, false, false] : List Bool).getD c.a0.val false
def v161 (c : Candidate) : Bool := ([true, true, false, false] : List Bool).getD c.b0.val false
def v162 (c : Candidate) : Bool := if (v2 c) then (v160 c) && (v161 c) else (v160 c) || (v161 c)
def v163 (c : Candidate) : Bool := ([true, true, false, false, (v162 c)] : List Bool).getD c.a1.val false
def v164 (c : Candidate) : Bool := ([true, true, false, false, (v162 c)] : List Bool).getD c.b1.val false
def v165 (c : Candidate) : Bool := if (v17 c) then (v163 c) && (v164 c) else (v163 c) || (v164 c)
def v166 (c : Candidate) : Bool := ([true, true, false, false, (v162 c), (v165 c)] : List Bool).getD c.a2.val false
def v167 (c : Candidate) : Bool := ([true, true, false, false, (v162 c), (v165 c)] : List Bool).getD c.b2.val false
def v168 (c : Candidate) : Bool := if (v36 c) then (v166 c) && (v167 c) else (v166 c) || (v167 c)
def v169 (c : Candidate) : Bool := ([true, true, false, false, (v162 c), (v165 c), (v168 c)] : List Bool).getD c.a3.val false
def v170 (c : Candidate) : Bool := ([true, true, false, false, (v162 c), (v165 c), (v168 c)] : List Bool).getD c.b3.val false
def v171 (c : Candidate) : Bool := if (v59 c) then (v169 c) && (v170 c) else (v169 c) || (v170 c)
def v172 (c : Candidate) : Bool := ([true, true, false, false, (v162 c), (v165 c), (v168 c), (v171 c)] : List Bool).getD c.a4.val false
def v173 (c : Candidate) : Bool := ([true, true, false, false, (v162 c), (v165 c), (v168 c), (v171 c)] : List Bool).getD c.b4.val false
def v174 (c : Candidate) : Bool := if (v86 c) then (v172 c) && (v173 c) else (v172 c) || (v173 c)
def v175 (c : Candidate) : Bool := ([false, false, true, false] : List Bool).getD c.a0.val false
def v176 (c : Candidate) : Bool := ([false, false, true, false] : List Bool).getD c.b0.val false
def v177 (c : Candidate) : Bool := if (v2 c) then (v175 c) && (v176 c) else (v175 c) || (v176 c)
def v178 (c : Candidate) : Bool := ([false, false, true, false, (v177 c)] : List Bool).getD c.a1.val false
def v179 (c : Candidate) : Bool := ([false, false, true, false, (v177 c)] : List Bool).getD c.b1.val false
def v180 (c : Candidate) : Bool := if (v17 c) then (v178 c) && (v179 c) else (v178 c) || (v179 c)
def v181 (c : Candidate) : Bool := ([false, false, true, false, (v177 c), (v180 c)] : List Bool).getD c.a2.val false
def v182 (c : Candidate) : Bool := ([false, false, true, false, (v177 c), (v180 c)] : List Bool).getD c.b2.val false
def v183 (c : Candidate) : Bool := if (v36 c) then (v181 c) && (v182 c) else (v181 c) || (v182 c)
def v184 (c : Candidate) : Bool := ([false, false, true, false, (v177 c), (v180 c), (v183 c)] : List Bool).getD c.a3.val false
def v185 (c : Candidate) : Bool := ([false, false, true, false, (v177 c), (v180 c), (v183 c)] : List Bool).getD c.b3.val false
def v186 (c : Candidate) : Bool := if (v59 c) then (v184 c) && (v185 c) else (v184 c) || (v185 c)
def v187 (c : Candidate) : Bool := ([false, false, true, false, (v177 c), (v180 c), (v183 c), (v186 c)] : List Bool).getD c.a4.val false
def v188 (c : Candidate) : Bool := ([false, false, true, false, (v177 c), (v180 c), (v183 c), (v186 c)] : List Bool).getD c.b4.val false
def v189 (c : Candidate) : Bool := if (v86 c) then (v187 c) && (v188 c) else (v187 c) || (v188 c)
def v190 (c : Candidate) : Bool := ([true, false, true, false] : List Bool).getD c.a0.val false
def v191 (c : Candidate) : Bool := ([true, false, true, false] : List Bool).getD c.b0.val false
def v192 (c : Candidate) : Bool := if (v2 c) then (v190 c) && (v191 c) else (v190 c) || (v191 c)
def v193 (c : Candidate) : Bool := ([true, false, true, false, (v192 c)] : List Bool).getD c.a1.val false
def v194 (c : Candidate) : Bool := ([true, false, true, false, (v192 c)] : List Bool).getD c.b1.val false
def v195 (c : Candidate) : Bool := if (v17 c) then (v193 c) && (v194 c) else (v193 c) || (v194 c)
def v196 (c : Candidate) : Bool := ([true, false, true, false, (v192 c), (v195 c)] : List Bool).getD c.a2.val false
def v197 (c : Candidate) : Bool := ([true, false, true, false, (v192 c), (v195 c)] : List Bool).getD c.b2.val false
def v198 (c : Candidate) : Bool := if (v36 c) then (v196 c) && (v197 c) else (v196 c) || (v197 c)
def v199 (c : Candidate) : Bool := ([true, false, true, false, (v192 c), (v195 c), (v198 c)] : List Bool).getD c.a3.val false
def v200 (c : Candidate) : Bool := ([true, false, true, false, (v192 c), (v195 c), (v198 c)] : List Bool).getD c.b3.val false
def v201 (c : Candidate) : Bool := if (v59 c) then (v199 c) && (v200 c) else (v199 c) || (v200 c)
def v202 (c : Candidate) : Bool := ([true, false, true, false, (v192 c), (v195 c), (v198 c), (v201 c)] : List Bool).getD c.a4.val false
def v203 (c : Candidate) : Bool := ([true, false, true, false, (v192 c), (v195 c), (v198 c), (v201 c)] : List Bool).getD c.b4.val false
def v204 (c : Candidate) : Bool := if (v86 c) then (v202 c) && (v203 c) else (v202 c) || (v203 c)
def v205 (c : Candidate) : Bool := ([false, true, true, false] : List Bool).getD c.a0.val false
def v206 (c : Candidate) : Bool := ([false, true, true, false] : List Bool).getD c.b0.val false
def v207 (c : Candidate) : Bool := if (v2 c) then (v205 c) && (v206 c) else (v205 c) || (v206 c)
def v208 (c : Candidate) : Bool := ([false, true, true, false, (v207 c)] : List Bool).getD c.a1.val false
def v209 (c : Candidate) : Bool := ([false, true, true, false, (v207 c)] : List Bool).getD c.b1.val false
def v210 (c : Candidate) : Bool := if (v17 c) then (v208 c) && (v209 c) else (v208 c) || (v209 c)
def v211 (c : Candidate) : Bool := ([false, true, true, false, (v207 c), (v210 c)] : List Bool).getD c.a2.val false
def v212 (c : Candidate) : Bool := ([false, true, true, false, (v207 c), (v210 c)] : List Bool).getD c.b2.val false
def v213 (c : Candidate) : Bool := if (v36 c) then (v211 c) && (v212 c) else (v211 c) || (v212 c)
def v214 (c : Candidate) : Bool := ([false, true, true, false, (v207 c), (v210 c), (v213 c)] : List Bool).getD c.a3.val false
def v215 (c : Candidate) : Bool := ([false, true, true, false, (v207 c), (v210 c), (v213 c)] : List Bool).getD c.b3.val false
def v216 (c : Candidate) : Bool := if (v59 c) then (v214 c) && (v215 c) else (v214 c) || (v215 c)
def v217 (c : Candidate) : Bool := ([false, true, true, false, (v207 c), (v210 c), (v213 c), (v216 c)] : List Bool).getD c.a4.val false
def v218 (c : Candidate) : Bool := ([false, true, true, false, (v207 c), (v210 c), (v213 c), (v216 c)] : List Bool).getD c.b4.val false
def v219 (c : Candidate) : Bool := if (v86 c) then (v217 c) && (v218 c) else (v217 c) || (v218 c)
def v220 (c : Candidate) : Bool := ([true, true, true, false] : List Bool).getD c.a0.val false
def v221 (c : Candidate) : Bool := ([true, true, true, false] : List Bool).getD c.b0.val false
def v222 (c : Candidate) : Bool := if (v2 c) then (v220 c) && (v221 c) else (v220 c) || (v221 c)
def v223 (c : Candidate) : Bool := ([true, true, true, false, (v222 c)] : List Bool).getD c.a1.val false
def v224 (c : Candidate) : Bool := ([true, true, true, false, (v222 c)] : List Bool).getD c.b1.val false
def v225 (c : Candidate) : Bool := if (v17 c) then (v223 c) && (v224 c) else (v223 c) || (v224 c)
def v226 (c : Candidate) : Bool := ([true, true, true, false, (v222 c), (v225 c)] : List Bool).getD c.a2.val false
def v227 (c : Candidate) : Bool := ([true, true, true, false, (v222 c), (v225 c)] : List Bool).getD c.b2.val false
def v228 (c : Candidate) : Bool := if (v36 c) then (v226 c) && (v227 c) else (v226 c) || (v227 c)
def v229 (c : Candidate) : Bool := ([true, true, true, false, (v222 c), (v225 c), (v228 c)] : List Bool).getD c.a3.val false
def v230 (c : Candidate) : Bool := ([true, true, true, false, (v222 c), (v225 c), (v228 c)] : List Bool).getD c.b3.val false
def v231 (c : Candidate) : Bool := if (v59 c) then (v229 c) && (v230 c) else (v229 c) || (v230 c)
def v232 (c : Candidate) : Bool := ([true, true, true, false, (v222 c), (v225 c), (v228 c), (v231 c)] : List Bool).getD c.a4.val false
def v233 (c : Candidate) : Bool := ([true, true, true, false, (v222 c), (v225 c), (v228 c), (v231 c)] : List Bool).getD c.b4.val false
def v234 (c : Candidate) : Bool := if (v86 c) then (v232 c) && (v233 c) else (v232 c) || (v233 c)
def v235 (c : Candidate) : Bool := ([false, false, false, true] : List Bool).getD c.a0.val false
def v236 (c : Candidate) : Bool := ([false, false, false, true] : List Bool).getD c.b0.val false
def v237 (c : Candidate) : Bool := if (v2 c) then (v235 c) && (v236 c) else (v235 c) || (v236 c)
def v238 (c : Candidate) : Bool := ([false, false, false, true, (v237 c)] : List Bool).getD c.a1.val false
def v239 (c : Candidate) : Bool := ([false, false, false, true, (v237 c)] : List Bool).getD c.b1.val false
def v240 (c : Candidate) : Bool := if (v17 c) then (v238 c) && (v239 c) else (v238 c) || (v239 c)
def v241 (c : Candidate) : Bool := ([false, false, false, true, (v237 c), (v240 c)] : List Bool).getD c.a2.val false
def v242 (c : Candidate) : Bool := ([false, false, false, true, (v237 c), (v240 c)] : List Bool).getD c.b2.val false
def v243 (c : Candidate) : Bool := if (v36 c) then (v241 c) && (v242 c) else (v241 c) || (v242 c)
def v244 (c : Candidate) : Bool := ([false, false, false, true, (v237 c), (v240 c), (v243 c)] : List Bool).getD c.a3.val false
def v245 (c : Candidate) : Bool := ([false, false, false, true, (v237 c), (v240 c), (v243 c)] : List Bool).getD c.b3.val false
def v246 (c : Candidate) : Bool := if (v59 c) then (v244 c) && (v245 c) else (v244 c) || (v245 c)
def v247 (c : Candidate) : Bool := ([false, false, false, true, (v237 c), (v240 c), (v243 c), (v246 c)] : List Bool).getD c.a4.val false
def v248 (c : Candidate) : Bool := ([false, false, false, true, (v237 c), (v240 c), (v243 c), (v246 c)] : List Bool).getD c.b4.val false
def v249 (c : Candidate) : Bool := if (v86 c) then (v247 c) && (v248 c) else (v247 c) || (v248 c)
def v250 (c : Candidate) : Bool := ([true, false, false, true] : List Bool).getD c.a0.val false
def v251 (c : Candidate) : Bool := ([true, false, false, true] : List Bool).getD c.b0.val false
def v252 (c : Candidate) : Bool := if (v2 c) then (v250 c) && (v251 c) else (v250 c) || (v251 c)
def v253 (c : Candidate) : Bool := ([true, false, false, true, (v252 c)] : List Bool).getD c.a1.val false
def v254 (c : Candidate) : Bool := ([true, false, false, true, (v252 c)] : List Bool).getD c.b1.val false
def v255 (c : Candidate) : Bool := if (v17 c) then (v253 c) && (v254 c) else (v253 c) || (v254 c)
def v256 (c : Candidate) : Bool := ([true, false, false, true, (v252 c), (v255 c)] : List Bool).getD c.a2.val false
def v257 (c : Candidate) : Bool := ([true, false, false, true, (v252 c), (v255 c)] : List Bool).getD c.b2.val false
def v258 (c : Candidate) : Bool := if (v36 c) then (v256 c) && (v257 c) else (v256 c) || (v257 c)
def v259 (c : Candidate) : Bool := ([true, false, false, true, (v252 c), (v255 c), (v258 c)] : List Bool).getD c.a3.val false
def v260 (c : Candidate) : Bool := ([true, false, false, true, (v252 c), (v255 c), (v258 c)] : List Bool).getD c.b3.val false
def v261 (c : Candidate) : Bool := if (v59 c) then (v259 c) && (v260 c) else (v259 c) || (v260 c)
def v262 (c : Candidate) : Bool := ([true, false, false, true, (v252 c), (v255 c), (v258 c), (v261 c)] : List Bool).getD c.a4.val false
def v263 (c : Candidate) : Bool := ([true, false, false, true, (v252 c), (v255 c), (v258 c), (v261 c)] : List Bool).getD c.b4.val false
def v264 (c : Candidate) : Bool := if (v86 c) then (v262 c) && (v263 c) else (v262 c) || (v263 c)
def v265 (c : Candidate) : Bool := ([false, true, false, true] : List Bool).getD c.a0.val false
def v266 (c : Candidate) : Bool := ([false, true, false, true] : List Bool).getD c.b0.val false
def v267 (c : Candidate) : Bool := if (v2 c) then (v265 c) && (v266 c) else (v265 c) || (v266 c)
def v268 (c : Candidate) : Bool := ([false, true, false, true, (v267 c)] : List Bool).getD c.a1.val false
def v269 (c : Candidate) : Bool := ([false, true, false, true, (v267 c)] : List Bool).getD c.b1.val false
def v270 (c : Candidate) : Bool := if (v17 c) then (v268 c) && (v269 c) else (v268 c) || (v269 c)
def v271 (c : Candidate) : Bool := ([false, true, false, true, (v267 c), (v270 c)] : List Bool).getD c.a2.val false
def v272 (c : Candidate) : Bool := ([false, true, false, true, (v267 c), (v270 c)] : List Bool).getD c.b2.val false
def v273 (c : Candidate) : Bool := if (v36 c) then (v271 c) && (v272 c) else (v271 c) || (v272 c)
def v274 (c : Candidate) : Bool := ([false, true, false, true, (v267 c), (v270 c), (v273 c)] : List Bool).getD c.a3.val false
def v275 (c : Candidate) : Bool := ([false, true, false, true, (v267 c), (v270 c), (v273 c)] : List Bool).getD c.b3.val false
def v276 (c : Candidate) : Bool := if (v59 c) then (v274 c) && (v275 c) else (v274 c) || (v275 c)
def v277 (c : Candidate) : Bool := ([false, true, false, true, (v267 c), (v270 c), (v273 c), (v276 c)] : List Bool).getD c.a4.val false
def v278 (c : Candidate) : Bool := ([false, true, false, true, (v267 c), (v270 c), (v273 c), (v276 c)] : List Bool).getD c.b4.val false
def v279 (c : Candidate) : Bool := if (v86 c) then (v277 c) && (v278 c) else (v277 c) || (v278 c)
def v280 (c : Candidate) : Bool := ([true, true, false, true] : List Bool).getD c.a0.val false
def v281 (c : Candidate) : Bool := ([true, true, false, true] : List Bool).getD c.b0.val false
def v282 (c : Candidate) : Bool := if (v2 c) then (v280 c) && (v281 c) else (v280 c) || (v281 c)
def v283 (c : Candidate) : Bool := ([true, true, false, true, (v282 c)] : List Bool).getD c.a1.val false
def v284 (c : Candidate) : Bool := ([true, true, false, true, (v282 c)] : List Bool).getD c.b1.val false
def v285 (c : Candidate) : Bool := if (v17 c) then (v283 c) && (v284 c) else (v283 c) || (v284 c)
def v286 (c : Candidate) : Bool := ([true, true, false, true, (v282 c), (v285 c)] : List Bool).getD c.a2.val false
def v287 (c : Candidate) : Bool := ([true, true, false, true, (v282 c), (v285 c)] : List Bool).getD c.b2.val false
def v288 (c : Candidate) : Bool := if (v36 c) then (v286 c) && (v287 c) else (v286 c) || (v287 c)
def v289 (c : Candidate) : Bool := ([true, true, false, true, (v282 c), (v285 c), (v288 c)] : List Bool).getD c.a3.val false
def v290 (c : Candidate) : Bool := ([true, true, false, true, (v282 c), (v285 c), (v288 c)] : List Bool).getD c.b3.val false
def v291 (c : Candidate) : Bool := if (v59 c) then (v289 c) && (v290 c) else (v289 c) || (v290 c)
def v292 (c : Candidate) : Bool := ([true, true, false, true, (v282 c), (v285 c), (v288 c), (v291 c)] : List Bool).getD c.a4.val false
def v293 (c : Candidate) : Bool := ([true, true, false, true, (v282 c), (v285 c), (v288 c), (v291 c)] : List Bool).getD c.b4.val false
def v294 (c : Candidate) : Bool := if (v86 c) then (v292 c) && (v293 c) else (v292 c) || (v293 c)
def v295 (c : Candidate) : Bool := ([false, false, true, true] : List Bool).getD c.a0.val false
def v296 (c : Candidate) : Bool := ([false, false, true, true] : List Bool).getD c.b0.val false
def v297 (c : Candidate) : Bool := if (v2 c) then (v295 c) && (v296 c) else (v295 c) || (v296 c)
def v298 (c : Candidate) : Bool := ([false, false, true, true, (v297 c)] : List Bool).getD c.a1.val false
def v299 (c : Candidate) : Bool := ([false, false, true, true, (v297 c)] : List Bool).getD c.b1.val false
def v300 (c : Candidate) : Bool := if (v17 c) then (v298 c) && (v299 c) else (v298 c) || (v299 c)
def v301 (c : Candidate) : Bool := ([false, false, true, true, (v297 c), (v300 c)] : List Bool).getD c.a2.val false
def v302 (c : Candidate) : Bool := ([false, false, true, true, (v297 c), (v300 c)] : List Bool).getD c.b2.val false
def v303 (c : Candidate) : Bool := if (v36 c) then (v301 c) && (v302 c) else (v301 c) || (v302 c)
def v304 (c : Candidate) : Bool := ([false, false, true, true, (v297 c), (v300 c), (v303 c)] : List Bool).getD c.a3.val false
def v305 (c : Candidate) : Bool := ([false, false, true, true, (v297 c), (v300 c), (v303 c)] : List Bool).getD c.b3.val false
def v306 (c : Candidate) : Bool := if (v59 c) then (v304 c) && (v305 c) else (v304 c) || (v305 c)
def v307 (c : Candidate) : Bool := ([false, false, true, true, (v297 c), (v300 c), (v303 c), (v306 c)] : List Bool).getD c.a4.val false
def v308 (c : Candidate) : Bool := ([false, false, true, true, (v297 c), (v300 c), (v303 c), (v306 c)] : List Bool).getD c.b4.val false
def v309 (c : Candidate) : Bool := if (v86 c) then (v307 c) && (v308 c) else (v307 c) || (v308 c)
def v310 (c : Candidate) : Bool := ([true, false, true, true] : List Bool).getD c.a0.val false
def v311 (c : Candidate) : Bool := ([true, false, true, true] : List Bool).getD c.b0.val false
def v312 (c : Candidate) : Bool := if (v2 c) then (v310 c) && (v311 c) else (v310 c) || (v311 c)
def v313 (c : Candidate) : Bool := ([true, false, true, true, (v312 c)] : List Bool).getD c.a1.val false
def v314 (c : Candidate) : Bool := ([true, false, true, true, (v312 c)] : List Bool).getD c.b1.val false
def v315 (c : Candidate) : Bool := if (v17 c) then (v313 c) && (v314 c) else (v313 c) || (v314 c)
def v316 (c : Candidate) : Bool := ([true, false, true, true, (v312 c), (v315 c)] : List Bool).getD c.a2.val false
def v317 (c : Candidate) : Bool := ([true, false, true, true, (v312 c), (v315 c)] : List Bool).getD c.b2.val false
def v318 (c : Candidate) : Bool := if (v36 c) then (v316 c) && (v317 c) else (v316 c) || (v317 c)
def v319 (c : Candidate) : Bool := ([true, false, true, true, (v312 c), (v315 c), (v318 c)] : List Bool).getD c.a3.val false
def v320 (c : Candidate) : Bool := ([true, false, true, true, (v312 c), (v315 c), (v318 c)] : List Bool).getD c.b3.val false
def v321 (c : Candidate) : Bool := if (v59 c) then (v319 c) && (v320 c) else (v319 c) || (v320 c)
def v322 (c : Candidate) : Bool := ([true, false, true, true, (v312 c), (v315 c), (v318 c), (v321 c)] : List Bool).getD c.a4.val false
def v323 (c : Candidate) : Bool := ([true, false, true, true, (v312 c), (v315 c), (v318 c), (v321 c)] : List Bool).getD c.b4.val false
def v324 (c : Candidate) : Bool := if (v86 c) then (v322 c) && (v323 c) else (v322 c) || (v323 c)
def v325 (c : Candidate) : Bool := ([false, true, true, true] : List Bool).getD c.a0.val false
def v326 (c : Candidate) : Bool := ([false, true, true, true] : List Bool).getD c.b0.val false
def v327 (c : Candidate) : Bool := if (v2 c) then (v325 c) && (v326 c) else (v325 c) || (v326 c)
def v328 (c : Candidate) : Bool := ([false, true, true, true, (v327 c)] : List Bool).getD c.a1.val false
def v329 (c : Candidate) : Bool := ([false, true, true, true, (v327 c)] : List Bool).getD c.b1.val false
def v330 (c : Candidate) : Bool := if (v17 c) then (v328 c) && (v329 c) else (v328 c) || (v329 c)
def v331 (c : Candidate) : Bool := ([false, true, true, true, (v327 c), (v330 c)] : List Bool).getD c.a2.val false
def v332 (c : Candidate) : Bool := ([false, true, true, true, (v327 c), (v330 c)] : List Bool).getD c.b2.val false
def v333 (c : Candidate) : Bool := if (v36 c) then (v331 c) && (v332 c) else (v331 c) || (v332 c)
def v334 (c : Candidate) : Bool := ([false, true, true, true, (v327 c), (v330 c), (v333 c)] : List Bool).getD c.a3.val false
def v335 (c : Candidate) : Bool := ([false, true, true, true, (v327 c), (v330 c), (v333 c)] : List Bool).getD c.b3.val false
def v336 (c : Candidate) : Bool := if (v59 c) then (v334 c) && (v335 c) else (v334 c) || (v335 c)
def v337 (c : Candidate) : Bool := ([false, true, true, true, (v327 c), (v330 c), (v333 c), (v336 c)] : List Bool).getD c.a4.val false
def v338 (c : Candidate) : Bool := ([false, true, true, true, (v327 c), (v330 c), (v333 c), (v336 c)] : List Bool).getD c.b4.val false
def v339 (c : Candidate) : Bool := if (v86 c) then (v337 c) && (v338 c) else (v337 c) || (v338 c)
def v340 (c : Candidate) : Bool := if (v2 c) then true && true else true || true
def v341 (c : Candidate) : Bool := ([true, true, true, true, (v340 c)] : List Bool).getD c.a1.val false
def v342 (c : Candidate) : Bool := ([true, true, true, true, (v340 c)] : List Bool).getD c.b1.val false
def v343 (c : Candidate) : Bool := if (v17 c) then (v341 c) && (v342 c) else (v341 c) || (v342 c)
def v344 (c : Candidate) : Bool := ([true, true, true, true, (v340 c), (v343 c)] : List Bool).getD c.a2.val false
def v345 (c : Candidate) : Bool := ([true, true, true, true, (v340 c), (v343 c)] : List Bool).getD c.b2.val false
def v346 (c : Candidate) : Bool := if (v36 c) then (v344 c) && (v345 c) else (v344 c) || (v345 c)
def v347 (c : Candidate) : Bool := ([true, true, true, true, (v340 c), (v343 c), (v346 c)] : List Bool).getD c.a3.val false
def v348 (c : Candidate) : Bool := ([true, true, true, true, (v340 c), (v343 c), (v346 c)] : List Bool).getD c.b3.val false
def v349 (c : Candidate) : Bool := if (v59 c) then (v347 c) && (v348 c) else (v347 c) || (v348 c)
def v350 (c : Candidate) : Bool := ([true, true, true, true, (v340 c), (v343 c), (v346 c), (v349 c)] : List Bool).getD c.a4.val false
def v351 (c : Candidate) : Bool := ([true, true, true, true, (v340 c), (v343 c), (v346 c), (v349 c)] : List Bool).getD c.b4.val false
def v352 (c : Candidate) : Bool := if (v86 c) then (v350 c) && (v351 c) else (v350 c) || (v351 c)
def v353 (c : Candidate) : Bool := ([true, false, false, false] : List Bool).getD c.a0.val false
def v354 (c : Candidate) : Bool := ([true, false, false, false] : List Bool).getD c.b0.val false
def v355 (c : Candidate) : Bool := if (v2 c) then (v353 c) && (v354 c) else (v353 c) || (v354 c)
def v356 (c : Candidate) : Bool := ([true, false, false, false, (v355 c)] : List Bool).getD c.a1.val false
def v357 (c : Candidate) : Bool := ([true, false, false, false, (v355 c)] : List Bool).getD c.b1.val false
def v358 (c : Candidate) : Bool := if (v17 c) then (v356 c) && (v357 c) else (v356 c) || (v357 c)
def v359 (c : Candidate) : Bool := ([true, false, false, false, (v355 c), (v358 c)] : List Bool).getD c.a2.val false
def v360 (c : Candidate) : Bool := ([true, false, false, false, (v355 c), (v358 c)] : List Bool).getD c.b2.val false
def v361 (c : Candidate) : Bool := if (v36 c) then (v359 c) && (v360 c) else (v359 c) || (v360 c)
def v362 (c : Candidate) : Bool := ([true, false, false, false, (v355 c), (v358 c), (v361 c)] : List Bool).getD c.a3.val false
def v363 (c : Candidate) : Bool := ([true, false, false, false, (v355 c), (v358 c), (v361 c)] : List Bool).getD c.b3.val false
def v364 (c : Candidate) : Bool := if (v59 c) then (v362 c) && (v363 c) else (v362 c) || (v363 c)
def v365 (c : Candidate) : Bool := ([true, false, false, false, (v355 c), (v358 c), (v361 c), (v364 c)] : List Bool).getD c.a4.val false
def v366 (c : Candidate) : Bool := ([true, false, false, false, (v355 c), (v358 c), (v361 c), (v364 c)] : List Bool).getD c.b4.val false
def v367 (c : Candidate) : Bool := if (v86 c) then (v365 c) && (v366 c) else (v365 c) || (v366 c)
def v368 (c : Candidate) : Bool := ([false, true, false, false] : List Bool).getD c.a0.val false
def v369 (c : Candidate) : Bool := ([false, true, false, false] : List Bool).getD c.b0.val false
def v370 (c : Candidate) : Bool := (v353 c) && (v369 c)
def v371 (c : Candidate) : Bool := (v368 c) && (v354 c)
def v372 (c : Candidate) : Bool := !(v370 c) && !(v371 c)
def v373 (c : Candidate) : Bool := !(v368 c) && !(v369 c)
def v374 (c : Candidate) : Bool := if (v2 c) then !(v372 c) else !(v373 c)
def v375 (c : Candidate) : Bool := ([false, true, false, false, (v374 c)] : List Bool).getD c.a1.val false
def v376 (c : Candidate) : Bool := ([false, true, false, false, (v374 c)] : List Bool).getD c.b1.val false
def v377 (c : Candidate) : Bool := (v356 c) && (v376 c)
def v378 (c : Candidate) : Bool := (v375 c) && (v357 c)
def v379 (c : Candidate) : Bool := !(v377 c) && !(v378 c)
def v380 (c : Candidate) : Bool := !(v375 c) && !(v376 c)
def v381 (c : Candidate) : Bool := if (v17 c) then !(v379 c) else !(v380 c)
def v382 (c : Candidate) : Bool := ([false, true, false, false, (v374 c), (v381 c)] : List Bool).getD c.a2.val false
def v383 (c : Candidate) : Bool := ([false, true, false, false, (v374 c), (v381 c)] : List Bool).getD c.b2.val false
def v384 (c : Candidate) : Bool := (v359 c) && (v383 c)
def v385 (c : Candidate) : Bool := (v382 c) && (v360 c)
def v386 (c : Candidate) : Bool := !(v384 c) && !(v385 c)
def v387 (c : Candidate) : Bool := !(v382 c) && !(v383 c)
def v388 (c : Candidate) : Bool := if (v36 c) then !(v386 c) else !(v387 c)
def v389 (c : Candidate) : Bool := ([false, true, false, false, (v374 c), (v381 c), (v388 c)] : List Bool).getD c.a3.val false
def v390 (c : Candidate) : Bool := ([false, true, false, false, (v374 c), (v381 c), (v388 c)] : List Bool).getD c.b3.val false
def v391 (c : Candidate) : Bool := (v362 c) && (v390 c)
def v392 (c : Candidate) : Bool := (v389 c) && (v363 c)
def v393 (c : Candidate) : Bool := !(v391 c) && !(v392 c)
def v394 (c : Candidate) : Bool := !(v389 c) && !(v390 c)
def v395 (c : Candidate) : Bool := if (v59 c) then !(v393 c) else !(v394 c)
def v396 (c : Candidate) : Bool := ([false, true, false, false, (v374 c), (v381 c), (v388 c), (v395 c)] : List Bool).getD c.a4.val false
def v397 (c : Candidate) : Bool := ([false, true, false, false, (v374 c), (v381 c), (v388 c), (v395 c)] : List Bool).getD c.b4.val false
def v398 (c : Candidate) : Bool := (v365 c) && (v397 c)
def v399 (c : Candidate) : Bool := (v396 c) && (v366 c)
def v400 (c : Candidate) : Bool := !(v398 c) && !(v399 c)
def v401 (c : Candidate) : Bool := !(v396 c) && !(v397 c)
def v402 (c : Candidate) : Bool := if (v86 c) then !(v400 c) else !(v401 c)
def v403 (c : Candidate) : Bool := ([false, true, false, false] : List Bool).getD c.a0.val false
def v404 (c : Candidate) : Bool := ([false, true, false, false] : List Bool).getD c.b0.val false
def v405 (c : Candidate) : Bool := if (v2 c) then (v403 c) && (v404 c) else (v403 c) || (v404 c)
def v406 (c : Candidate) : Bool := ([false, true, false, false, (v405 c)] : List Bool).getD c.a1.val false
def v407 (c : Candidate) : Bool := ([false, true, false, false, (v405 c)] : List Bool).getD c.b1.val false
def v408 (c : Candidate) : Bool := if (v17 c) then (v406 c) && (v407 c) else (v406 c) || (v407 c)
def v409 (c : Candidate) : Bool := ([false, true, false, false, (v405 c), (v408 c)] : List Bool).getD c.a2.val false
def v410 (c : Candidate) : Bool := ([false, true, false, false, (v405 c), (v408 c)] : List Bool).getD c.b2.val false
def v411 (c : Candidate) : Bool := if (v36 c) then (v409 c) && (v410 c) else (v409 c) || (v410 c)
def v412 (c : Candidate) : Bool := ([false, true, false, false, (v405 c), (v408 c), (v411 c)] : List Bool).getD c.a3.val false
def v413 (c : Candidate) : Bool := ([false, true, false, false, (v405 c), (v408 c), (v411 c)] : List Bool).getD c.b3.val false
def v414 (c : Candidate) : Bool := if (v59 c) then (v412 c) && (v413 c) else (v412 c) || (v413 c)
def v415 (c : Candidate) : Bool := ([false, true, false, false, (v405 c), (v408 c), (v411 c), (v414 c)] : List Bool).getD c.a4.val false
def v416 (c : Candidate) : Bool := ([false, true, false, false, (v405 c), (v408 c), (v411 c), (v414 c)] : List Bool).getD c.b4.val false
def v417 (c : Candidate) : Bool := if (v86 c) then (v415 c) && (v416 c) else (v415 c) || (v416 c)
def v418 (c : Candidate) : Bool := ([true, false, false, false] : List Bool).getD c.a0.val false
def v419 (c : Candidate) : Bool := ([true, false, false, false] : List Bool).getD c.b0.val false
def v420 (c : Candidate) : Bool := (v403 c) && (v419 c)
def v421 (c : Candidate) : Bool := (v418 c) && (v404 c)
def v422 (c : Candidate) : Bool := !(v420 c) && !(v421 c)
def v423 (c : Candidate) : Bool := !(v418 c) && !(v419 c)
def v424 (c : Candidate) : Bool := if (v2 c) then !(v422 c) else !(v423 c)
def v425 (c : Candidate) : Bool := ([true, false, false, false, (v424 c)] : List Bool).getD c.a1.val false
def v426 (c : Candidate) : Bool := ([true, false, false, false, (v424 c)] : List Bool).getD c.b1.val false
def v427 (c : Candidate) : Bool := (v406 c) && (v426 c)
def v428 (c : Candidate) : Bool := (v425 c) && (v407 c)
def v429 (c : Candidate) : Bool := !(v427 c) && !(v428 c)
def v430 (c : Candidate) : Bool := !(v425 c) && !(v426 c)
def v431 (c : Candidate) : Bool := if (v17 c) then !(v429 c) else !(v430 c)
def v432 (c : Candidate) : Bool := ([true, false, false, false, (v424 c), (v431 c)] : List Bool).getD c.a2.val false
def v433 (c : Candidate) : Bool := ([true, false, false, false, (v424 c), (v431 c)] : List Bool).getD c.b2.val false
def v434 (c : Candidate) : Bool := (v409 c) && (v433 c)
def v435 (c : Candidate) : Bool := (v432 c) && (v410 c)
def v436 (c : Candidate) : Bool := !(v434 c) && !(v435 c)
def v437 (c : Candidate) : Bool := !(v432 c) && !(v433 c)
def v438 (c : Candidate) : Bool := if (v36 c) then !(v436 c) else !(v437 c)
def v439 (c : Candidate) : Bool := ([true, false, false, false, (v424 c), (v431 c), (v438 c)] : List Bool).getD c.a3.val false
def v440 (c : Candidate) : Bool := ([true, false, false, false, (v424 c), (v431 c), (v438 c)] : List Bool).getD c.b3.val false
def v441 (c : Candidate) : Bool := (v412 c) && (v440 c)
def v442 (c : Candidate) : Bool := (v439 c) && (v413 c)
def v443 (c : Candidate) : Bool := !(v441 c) && !(v442 c)
def v444 (c : Candidate) : Bool := !(v439 c) && !(v440 c)
def v445 (c : Candidate) : Bool := if (v59 c) then !(v443 c) else !(v444 c)
def v446 (c : Candidate) : Bool := ([true, false, false, false, (v424 c), (v431 c), (v438 c), (v445 c)] : List Bool).getD c.a4.val false
def v447 (c : Candidate) : Bool := ([true, false, false, false, (v424 c), (v431 c), (v438 c), (v445 c)] : List Bool).getD c.b4.val false
def v448 (c : Candidate) : Bool := (v415 c) && (v447 c)
def v449 (c : Candidate) : Bool := (v446 c) && (v416 c)
def v450 (c : Candidate) : Bool := !(v448 c) && !(v449 c)
def v451 (c : Candidate) : Bool := !(v446 c) && !(v447 c)
def v452 (c : Candidate) : Bool := if (v86 c) then !(v450 c) else !(v451 c)

def assignment (c : Candidate) (n : Nat) : Bool :=
  ([false, true, v2 c, v3 c, v4 c, v5 c, v6 c, v7 c, v8 c, v9 c, v10 c, v11 c, v12 c, v13 c, v14 c, v15 c, v16 c, v17 c, v18 c, v19 c, v20 c, v21 c, v22 c, v23 c, v24 c, v25 c, v26 c, v27 c, v28 c, v29 c, v30 c, v31 c, v32 c, v33 c, v34 c, v35 c, v36 c, v37 c, v38 c, v39 c, v40 c, v41 c, v42 c, v43 c, v44 c, v45 c, v46 c, v47 c, v48 c, v49 c, v50 c, v51 c, v52 c, v53 c, v54 c, v55 c, v56 c, v57 c, v58 c, v59 c, v60 c, v61 c, v62 c, v63 c, v64 c, v65 c, v66 c, v67 c, v68 c, v69 c, v70 c, v71 c, v72 c, v73 c, v74 c, v75 c, v76 c, v77 c, v78 c, v79 c, v80 c, v81 c, v82 c, v83 c, v84 c, v85 c, v86 c, v87 c, v88 c, v89 c, v90 c, v91 c, v92 c, v93 c, v94 c, v95 c, v96 c, v97 c, v98 c, v99 c, v100 c, v101 c, v102 c, v103 c, v104 c, v105 c, v106 c, v107 c, v108 c, v109 c, v110 c, v111 c, v112 c, v113 c, v114 c, v115 c, v116 c, v117 c, v118 c, v119 c, v120 c, v121 c, v122 c, v123 c, v124 c, v125 c, v126 c, v127 c, v128 c, v129 c, v130 c, v131 c, v132 c, v133 c, v134 c, v135 c, v136 c, v137 c, v138 c, v139 c, v140 c, v141 c, v142 c, v143 c, v144 c, v145 c, v146 c, v147 c, v148 c, v149 c, v150 c, v151 c, v152 c, v153 c, v154 c, v155 c, v156 c, v157 c, v158 c, v159 c, v160 c, v161 c, v162 c, v163 c, v164 c, v165 c, v166 c, v167 c, v168 c, v169 c, v170 c, v171 c, v172 c, v173 c, v174 c, v175 c, v176 c, v177 c, v178 c, v179 c, v180 c, v181 c, v182 c, v183 c, v184 c, v185 c, v186 c, v187 c, v188 c, v189 c, v190 c, v191 c, v192 c, v193 c, v194 c, v195 c, v196 c, v197 c, v198 c, v199 c, v200 c, v201 c, v202 c, v203 c, v204 c, v205 c, v206 c, v207 c, v208 c, v209 c, v210 c, v211 c, v212 c, v213 c, v214 c, v215 c, v216 c, v217 c, v218 c, v219 c, v220 c, v221 c, v222 c, v223 c, v224 c, v225 c, v226 c, v227 c, v228 c, v229 c, v230 c, v231 c, v232 c, v233 c, v234 c, v235 c, v236 c, v237 c, v238 c, v239 c, v240 c, v241 c, v242 c, v243 c, v244 c, v245 c, v246 c, v247 c, v248 c, v249 c, v250 c, v251 c, v252 c, v253 c, v254 c, v255 c, v256 c, v257 c, v258 c, v259 c, v260 c, v261 c, v262 c, v263 c, v264 c, v265 c, v266 c, v267 c, v268 c, v269 c, v270 c, v271 c, v272 c, v273 c, v274 c, v275 c, v276 c, v277 c, v278 c, v279 c, v280 c, v281 c, v282 c, v283 c, v284 c, v285 c, v286 c, v287 c, v288 c, v289 c, v290 c, v291 c, v292 c, v293 c, v294 c, v295 c, v296 c, v297 c, v298 c, v299 c, v300 c, v301 c, v302 c, v303 c, v304 c, v305 c, v306 c, v307 c, v308 c, v309 c, v310 c, v311 c, v312 c, v313 c, v314 c, v315 c, v316 c, v317 c, v318 c, v319 c, v320 c, v321 c, v322 c, v323 c, v324 c, v325 c, v326 c, v327 c, v328 c, v329 c, v330 c, v331 c, v332 c, v333 c, v334 c, v335 c, v336 c, v337 c, v338 c, v339 c, v340 c, v341 c, v342 c, v343 c, v344 c, v345 c, v346 c, v347 c, v348 c, v349 c, v350 c, v351 c, v352 c, v353 c, v354 c, v355 c, v356 c, v357 c, v358 c, v359 c, v360 c, v361 c, v362 c, v363 c, v364 c, v365 c, v366 c, v367 c, v368 c, v369 c, v370 c, v371 c, v372 c, v373 c, v374 c, v375 c, v376 c, v377 c, v378 c, v379 c, v380 c, v381 c, v382 c, v383 c, v384 c, v385 c, v386 c, v387 c, v388 c, v389 c, v390 c, v391 c, v392 c, v393 c, v394 c, v395 c, v396 c, v397 c, v398 c, v399 c, v400 c, v401 c, v402 c, v403 c, v404 c, v405 c, v406 c, v407 c, v408 c, v409 c, v410 c, v411 c, v412 c, v413 c, v414 c, v415 c, v416 c, v417 c, v418 c, v419 c, v420 c, v421 c, v422 c, v423 c, v424 c, v425 c, v426 c, v427 c, v428 c, v429 c, v430 c, v431 c, v432 c, v433 c, v434 c, v435 c, v436 c, v437 c, v438 c, v439 c, v440 c, v441 c, v442 c, v443 c, v444 c, v445 c, v446 c, v447 c, v448 c, v449 c, v450 c, v451 c, v452 c] : List Bool).getD n false

theorem assignment_1 (c : Candidate) : assignment c 1 = true := rfl
theorem assignment_2 (c : Candidate) : assignment c 2 = (v2 c) := rfl
theorem assignment_3 (c : Candidate) : assignment c 3 = (v3 c) := rfl
theorem assignment_4 (c : Candidate) : assignment c 4 = (v4 c) := rfl
theorem assignment_5 (c : Candidate) : assignment c 5 = (v5 c) := rfl
theorem assignment_6 (c : Candidate) : assignment c 6 = (v6 c) := rfl
theorem assignment_7 (c : Candidate) : assignment c 7 = (v7 c) := rfl
theorem assignment_8 (c : Candidate) : assignment c 8 = (v8 c) := rfl
theorem assignment_9 (c : Candidate) : assignment c 9 = (v9 c) := rfl
theorem assignment_10 (c : Candidate) : assignment c 10 = (v10 c) := rfl
theorem assignment_11 (c : Candidate) : assignment c 11 = (v11 c) := rfl
theorem assignment_12 (c : Candidate) : assignment c 12 = (v12 c) := rfl
theorem assignment_13 (c : Candidate) : assignment c 13 = (v13 c) := rfl
theorem assignment_14 (c : Candidate) : assignment c 14 = (v14 c) := rfl
theorem assignment_15 (c : Candidate) : assignment c 15 = (v15 c) := rfl
theorem assignment_16 (c : Candidate) : assignment c 16 = (v16 c) := rfl
theorem assignment_17 (c : Candidate) : assignment c 17 = (v17 c) := rfl
theorem assignment_18 (c : Candidate) : assignment c 18 = (v18 c) := rfl
theorem assignment_19 (c : Candidate) : assignment c 19 = (v19 c) := rfl
theorem assignment_20 (c : Candidate) : assignment c 20 = (v20 c) := rfl
theorem assignment_21 (c : Candidate) : assignment c 21 = (v21 c) := rfl
theorem assignment_22 (c : Candidate) : assignment c 22 = (v22 c) := rfl
theorem assignment_23 (c : Candidate) : assignment c 23 = (v23 c) := rfl
theorem assignment_24 (c : Candidate) : assignment c 24 = (v24 c) := rfl
theorem assignment_25 (c : Candidate) : assignment c 25 = (v25 c) := rfl
theorem assignment_26 (c : Candidate) : assignment c 26 = (v26 c) := rfl
theorem assignment_27 (c : Candidate) : assignment c 27 = (v27 c) := rfl
theorem assignment_28 (c : Candidate) : assignment c 28 = (v28 c) := rfl
theorem assignment_29 (c : Candidate) : assignment c 29 = (v29 c) := rfl
theorem assignment_30 (c : Candidate) : assignment c 30 = (v30 c) := rfl
theorem assignment_31 (c : Candidate) : assignment c 31 = (v31 c) := rfl
theorem assignment_32 (c : Candidate) : assignment c 32 = (v32 c) := rfl
theorem assignment_33 (c : Candidate) : assignment c 33 = (v33 c) := rfl
theorem assignment_34 (c : Candidate) : assignment c 34 = (v34 c) := rfl
theorem assignment_35 (c : Candidate) : assignment c 35 = (v35 c) := rfl
theorem assignment_36 (c : Candidate) : assignment c 36 = (v36 c) := rfl
theorem assignment_37 (c : Candidate) : assignment c 37 = (v37 c) := rfl
theorem assignment_38 (c : Candidate) : assignment c 38 = (v38 c) := rfl
theorem assignment_39 (c : Candidate) : assignment c 39 = (v39 c) := rfl
theorem assignment_40 (c : Candidate) : assignment c 40 = (v40 c) := rfl
theorem assignment_41 (c : Candidate) : assignment c 41 = (v41 c) := rfl
theorem assignment_42 (c : Candidate) : assignment c 42 = (v42 c) := rfl
theorem assignment_43 (c : Candidate) : assignment c 43 = (v43 c) := rfl
theorem assignment_44 (c : Candidate) : assignment c 44 = (v44 c) := rfl
theorem assignment_45 (c : Candidate) : assignment c 45 = (v45 c) := rfl
theorem assignment_46 (c : Candidate) : assignment c 46 = (v46 c) := rfl
theorem assignment_47 (c : Candidate) : assignment c 47 = (v47 c) := rfl
theorem assignment_48 (c : Candidate) : assignment c 48 = (v48 c) := rfl
theorem assignment_49 (c : Candidate) : assignment c 49 = (v49 c) := rfl
theorem assignment_50 (c : Candidate) : assignment c 50 = (v50 c) := rfl
theorem assignment_51 (c : Candidate) : assignment c 51 = (v51 c) := rfl
theorem assignment_52 (c : Candidate) : assignment c 52 = (v52 c) := rfl
theorem assignment_53 (c : Candidate) : assignment c 53 = (v53 c) := rfl
theorem assignment_54 (c : Candidate) : assignment c 54 = (v54 c) := rfl
theorem assignment_55 (c : Candidate) : assignment c 55 = (v55 c) := rfl
theorem assignment_56 (c : Candidate) : assignment c 56 = (v56 c) := rfl
theorem assignment_57 (c : Candidate) : assignment c 57 = (v57 c) := rfl
theorem assignment_58 (c : Candidate) : assignment c 58 = (v58 c) := rfl
theorem assignment_59 (c : Candidate) : assignment c 59 = (v59 c) := rfl
theorem assignment_60 (c : Candidate) : assignment c 60 = (v60 c) := rfl
theorem assignment_61 (c : Candidate) : assignment c 61 = (v61 c) := rfl
theorem assignment_62 (c : Candidate) : assignment c 62 = (v62 c) := rfl
theorem assignment_63 (c : Candidate) : assignment c 63 = (v63 c) := rfl
theorem assignment_64 (c : Candidate) : assignment c 64 = (v64 c) := rfl
theorem assignment_65 (c : Candidate) : assignment c 65 = (v65 c) := rfl
theorem assignment_66 (c : Candidate) : assignment c 66 = (v66 c) := rfl
theorem assignment_67 (c : Candidate) : assignment c 67 = (v67 c) := rfl
theorem assignment_68 (c : Candidate) : assignment c 68 = (v68 c) := rfl
theorem assignment_69 (c : Candidate) : assignment c 69 = (v69 c) := rfl
theorem assignment_70 (c : Candidate) : assignment c 70 = (v70 c) := rfl
theorem assignment_71 (c : Candidate) : assignment c 71 = (v71 c) := rfl
theorem assignment_72 (c : Candidate) : assignment c 72 = (v72 c) := rfl
theorem assignment_73 (c : Candidate) : assignment c 73 = (v73 c) := rfl
theorem assignment_74 (c : Candidate) : assignment c 74 = (v74 c) := rfl
theorem assignment_75 (c : Candidate) : assignment c 75 = (v75 c) := rfl
theorem assignment_76 (c : Candidate) : assignment c 76 = (v76 c) := rfl
theorem assignment_77 (c : Candidate) : assignment c 77 = (v77 c) := rfl
theorem assignment_78 (c : Candidate) : assignment c 78 = (v78 c) := rfl
theorem assignment_79 (c : Candidate) : assignment c 79 = (v79 c) := rfl
theorem assignment_80 (c : Candidate) : assignment c 80 = (v80 c) := rfl
theorem assignment_81 (c : Candidate) : assignment c 81 = (v81 c) := rfl
theorem assignment_82 (c : Candidate) : assignment c 82 = (v82 c) := rfl
theorem assignment_83 (c : Candidate) : assignment c 83 = (v83 c) := rfl
theorem assignment_84 (c : Candidate) : assignment c 84 = (v84 c) := rfl
theorem assignment_85 (c : Candidate) : assignment c 85 = (v85 c) := rfl
theorem assignment_86 (c : Candidate) : assignment c 86 = (v86 c) := rfl
theorem assignment_87 (c : Candidate) : assignment c 87 = (v87 c) := rfl
theorem assignment_88 (c : Candidate) : assignment c 88 = (v88 c) := rfl
theorem assignment_89 (c : Candidate) : assignment c 89 = (v89 c) := rfl
theorem assignment_90 (c : Candidate) : assignment c 90 = (v90 c) := rfl
theorem assignment_91 (c : Candidate) : assignment c 91 = (v91 c) := rfl
theorem assignment_92 (c : Candidate) : assignment c 92 = (v92 c) := rfl
theorem assignment_93 (c : Candidate) : assignment c 93 = (v93 c) := rfl
theorem assignment_94 (c : Candidate) : assignment c 94 = (v94 c) := rfl
theorem assignment_95 (c : Candidate) : assignment c 95 = (v95 c) := rfl
theorem assignment_96 (c : Candidate) : assignment c 96 = (v96 c) := rfl
theorem assignment_97 (c : Candidate) : assignment c 97 = (v97 c) := rfl
theorem assignment_98 (c : Candidate) : assignment c 98 = (v98 c) := rfl
theorem assignment_99 (c : Candidate) : assignment c 99 = (v99 c) := rfl
theorem assignment_100 (c : Candidate) : assignment c 100 = (v100 c) := rfl
theorem assignment_101 (c : Candidate) : assignment c 101 = (v101 c) := rfl
theorem assignment_102 (c : Candidate) : assignment c 102 = (v102 c) := rfl
theorem assignment_103 (c : Candidate) : assignment c 103 = (v103 c) := rfl
theorem assignment_104 (c : Candidate) : assignment c 104 = (v104 c) := rfl
theorem assignment_105 (c : Candidate) : assignment c 105 = (v105 c) := rfl
theorem assignment_106 (c : Candidate) : assignment c 106 = (v106 c) := rfl
theorem assignment_107 (c : Candidate) : assignment c 107 = (v107 c) := rfl
theorem assignment_108 (c : Candidate) : assignment c 108 = (v108 c) := rfl
theorem assignment_109 (c : Candidate) : assignment c 109 = (v109 c) := rfl
theorem assignment_110 (c : Candidate) : assignment c 110 = (v110 c) := rfl
theorem assignment_111 (c : Candidate) : assignment c 111 = (v111 c) := rfl
theorem assignment_112 (c : Candidate) : assignment c 112 = (v112 c) := rfl
theorem assignment_113 (c : Candidate) : assignment c 113 = (v113 c) := rfl
theorem assignment_114 (c : Candidate) : assignment c 114 = (v114 c) := rfl
theorem assignment_115 (c : Candidate) : assignment c 115 = (v115 c) := rfl
theorem assignment_116 (c : Candidate) : assignment c 116 = (v116 c) := rfl
theorem assignment_117 (c : Candidate) : assignment c 117 = (v117 c) := rfl
theorem assignment_118 (c : Candidate) : assignment c 118 = (v118 c) := rfl
theorem assignment_119 (c : Candidate) : assignment c 119 = (v119 c) := rfl
theorem assignment_120 (c : Candidate) : assignment c 120 = (v120 c) := rfl
theorem assignment_121 (c : Candidate) : assignment c 121 = (v121 c) := rfl
theorem assignment_122 (c : Candidate) : assignment c 122 = (v122 c) := rfl
theorem assignment_123 (c : Candidate) : assignment c 123 = (v123 c) := rfl
theorem assignment_124 (c : Candidate) : assignment c 124 = (v124 c) := rfl
theorem assignment_125 (c : Candidate) : assignment c 125 = (v125 c) := rfl
theorem assignment_126 (c : Candidate) : assignment c 126 = (v126 c) := rfl
theorem assignment_127 (c : Candidate) : assignment c 127 = (v127 c) := rfl
theorem assignment_128 (c : Candidate) : assignment c 128 = (v128 c) := rfl
theorem assignment_129 (c : Candidate) : assignment c 129 = (v129 c) := rfl
theorem assignment_130 (c : Candidate) : assignment c 130 = (v130 c) := rfl
theorem assignment_131 (c : Candidate) : assignment c 131 = (v131 c) := rfl
theorem assignment_132 (c : Candidate) : assignment c 132 = (v132 c) := rfl
theorem assignment_133 (c : Candidate) : assignment c 133 = (v133 c) := rfl
theorem assignment_134 (c : Candidate) : assignment c 134 = (v134 c) := rfl
theorem assignment_135 (c : Candidate) : assignment c 135 = (v135 c) := rfl
theorem assignment_136 (c : Candidate) : assignment c 136 = (v136 c) := rfl
theorem assignment_137 (c : Candidate) : assignment c 137 = (v137 c) := rfl
theorem assignment_138 (c : Candidate) : assignment c 138 = (v138 c) := rfl
theorem assignment_139 (c : Candidate) : assignment c 139 = (v139 c) := rfl
theorem assignment_140 (c : Candidate) : assignment c 140 = (v140 c) := rfl
theorem assignment_141 (c : Candidate) : assignment c 141 = (v141 c) := rfl
theorem assignment_142 (c : Candidate) : assignment c 142 = (v142 c) := rfl
theorem assignment_143 (c : Candidate) : assignment c 143 = (v143 c) := rfl
theorem assignment_144 (c : Candidate) : assignment c 144 = (v144 c) := rfl
theorem assignment_145 (c : Candidate) : assignment c 145 = (v145 c) := rfl
theorem assignment_146 (c : Candidate) : assignment c 146 = (v146 c) := rfl
theorem assignment_147 (c : Candidate) : assignment c 147 = (v147 c) := rfl
theorem assignment_148 (c : Candidate) : assignment c 148 = (v148 c) := rfl
theorem assignment_149 (c : Candidate) : assignment c 149 = (v149 c) := rfl
theorem assignment_150 (c : Candidate) : assignment c 150 = (v150 c) := rfl
theorem assignment_151 (c : Candidate) : assignment c 151 = (v151 c) := rfl
theorem assignment_152 (c : Candidate) : assignment c 152 = (v152 c) := rfl
theorem assignment_153 (c : Candidate) : assignment c 153 = (v153 c) := rfl
theorem assignment_154 (c : Candidate) : assignment c 154 = (v154 c) := rfl
theorem assignment_155 (c : Candidate) : assignment c 155 = (v155 c) := rfl
theorem assignment_156 (c : Candidate) : assignment c 156 = (v156 c) := rfl
theorem assignment_157 (c : Candidate) : assignment c 157 = (v157 c) := rfl
theorem assignment_158 (c : Candidate) : assignment c 158 = (v158 c) := rfl
theorem assignment_159 (c : Candidate) : assignment c 159 = (v159 c) := rfl
theorem assignment_160 (c : Candidate) : assignment c 160 = (v160 c) := rfl
theorem assignment_161 (c : Candidate) : assignment c 161 = (v161 c) := rfl
theorem assignment_162 (c : Candidate) : assignment c 162 = (v162 c) := rfl
theorem assignment_163 (c : Candidate) : assignment c 163 = (v163 c) := rfl
theorem assignment_164 (c : Candidate) : assignment c 164 = (v164 c) := rfl
theorem assignment_165 (c : Candidate) : assignment c 165 = (v165 c) := rfl
theorem assignment_166 (c : Candidate) : assignment c 166 = (v166 c) := rfl
theorem assignment_167 (c : Candidate) : assignment c 167 = (v167 c) := rfl
theorem assignment_168 (c : Candidate) : assignment c 168 = (v168 c) := rfl
theorem assignment_169 (c : Candidate) : assignment c 169 = (v169 c) := rfl
theorem assignment_170 (c : Candidate) : assignment c 170 = (v170 c) := rfl
theorem assignment_171 (c : Candidate) : assignment c 171 = (v171 c) := rfl
theorem assignment_172 (c : Candidate) : assignment c 172 = (v172 c) := rfl
theorem assignment_173 (c : Candidate) : assignment c 173 = (v173 c) := rfl
theorem assignment_174 (c : Candidate) : assignment c 174 = (v174 c) := rfl
theorem assignment_175 (c : Candidate) : assignment c 175 = (v175 c) := rfl
theorem assignment_176 (c : Candidate) : assignment c 176 = (v176 c) := rfl
theorem assignment_177 (c : Candidate) : assignment c 177 = (v177 c) := rfl
theorem assignment_178 (c : Candidate) : assignment c 178 = (v178 c) := rfl
theorem assignment_179 (c : Candidate) : assignment c 179 = (v179 c) := rfl
theorem assignment_180 (c : Candidate) : assignment c 180 = (v180 c) := rfl
theorem assignment_181 (c : Candidate) : assignment c 181 = (v181 c) := rfl
theorem assignment_182 (c : Candidate) : assignment c 182 = (v182 c) := rfl
theorem assignment_183 (c : Candidate) : assignment c 183 = (v183 c) := rfl
theorem assignment_184 (c : Candidate) : assignment c 184 = (v184 c) := rfl
theorem assignment_185 (c : Candidate) : assignment c 185 = (v185 c) := rfl
theorem assignment_186 (c : Candidate) : assignment c 186 = (v186 c) := rfl
theorem assignment_187 (c : Candidate) : assignment c 187 = (v187 c) := rfl
theorem assignment_188 (c : Candidate) : assignment c 188 = (v188 c) := rfl
theorem assignment_189 (c : Candidate) : assignment c 189 = (v189 c) := rfl
theorem assignment_190 (c : Candidate) : assignment c 190 = (v190 c) := rfl
theorem assignment_191 (c : Candidate) : assignment c 191 = (v191 c) := rfl
theorem assignment_192 (c : Candidate) : assignment c 192 = (v192 c) := rfl
theorem assignment_193 (c : Candidate) : assignment c 193 = (v193 c) := rfl
theorem assignment_194 (c : Candidate) : assignment c 194 = (v194 c) := rfl
theorem assignment_195 (c : Candidate) : assignment c 195 = (v195 c) := rfl
theorem assignment_196 (c : Candidate) : assignment c 196 = (v196 c) := rfl
theorem assignment_197 (c : Candidate) : assignment c 197 = (v197 c) := rfl
theorem assignment_198 (c : Candidate) : assignment c 198 = (v198 c) := rfl
theorem assignment_199 (c : Candidate) : assignment c 199 = (v199 c) := rfl
theorem assignment_200 (c : Candidate) : assignment c 200 = (v200 c) := rfl
theorem assignment_201 (c : Candidate) : assignment c 201 = (v201 c) := rfl
theorem assignment_202 (c : Candidate) : assignment c 202 = (v202 c) := rfl
theorem assignment_203 (c : Candidate) : assignment c 203 = (v203 c) := rfl
theorem assignment_204 (c : Candidate) : assignment c 204 = (v204 c) := rfl
theorem assignment_205 (c : Candidate) : assignment c 205 = (v205 c) := rfl
theorem assignment_206 (c : Candidate) : assignment c 206 = (v206 c) := rfl
theorem assignment_207 (c : Candidate) : assignment c 207 = (v207 c) := rfl
theorem assignment_208 (c : Candidate) : assignment c 208 = (v208 c) := rfl
theorem assignment_209 (c : Candidate) : assignment c 209 = (v209 c) := rfl
theorem assignment_210 (c : Candidate) : assignment c 210 = (v210 c) := rfl
theorem assignment_211 (c : Candidate) : assignment c 211 = (v211 c) := rfl
theorem assignment_212 (c : Candidate) : assignment c 212 = (v212 c) := rfl
theorem assignment_213 (c : Candidate) : assignment c 213 = (v213 c) := rfl
theorem assignment_214 (c : Candidate) : assignment c 214 = (v214 c) := rfl
theorem assignment_215 (c : Candidate) : assignment c 215 = (v215 c) := rfl
theorem assignment_216 (c : Candidate) : assignment c 216 = (v216 c) := rfl
theorem assignment_217 (c : Candidate) : assignment c 217 = (v217 c) := rfl
theorem assignment_218 (c : Candidate) : assignment c 218 = (v218 c) := rfl
theorem assignment_219 (c : Candidate) : assignment c 219 = (v219 c) := rfl
theorem assignment_220 (c : Candidate) : assignment c 220 = (v220 c) := rfl
theorem assignment_221 (c : Candidate) : assignment c 221 = (v221 c) := rfl
theorem assignment_222 (c : Candidate) : assignment c 222 = (v222 c) := rfl
theorem assignment_223 (c : Candidate) : assignment c 223 = (v223 c) := rfl
theorem assignment_224 (c : Candidate) : assignment c 224 = (v224 c) := rfl
theorem assignment_225 (c : Candidate) : assignment c 225 = (v225 c) := rfl
theorem assignment_226 (c : Candidate) : assignment c 226 = (v226 c) := rfl
theorem assignment_227 (c : Candidate) : assignment c 227 = (v227 c) := rfl
theorem assignment_228 (c : Candidate) : assignment c 228 = (v228 c) := rfl
theorem assignment_229 (c : Candidate) : assignment c 229 = (v229 c) := rfl
theorem assignment_230 (c : Candidate) : assignment c 230 = (v230 c) := rfl
theorem assignment_231 (c : Candidate) : assignment c 231 = (v231 c) := rfl
theorem assignment_232 (c : Candidate) : assignment c 232 = (v232 c) := rfl
theorem assignment_233 (c : Candidate) : assignment c 233 = (v233 c) := rfl
theorem assignment_234 (c : Candidate) : assignment c 234 = (v234 c) := rfl
theorem assignment_235 (c : Candidate) : assignment c 235 = (v235 c) := rfl
theorem assignment_236 (c : Candidate) : assignment c 236 = (v236 c) := rfl
theorem assignment_237 (c : Candidate) : assignment c 237 = (v237 c) := rfl
theorem assignment_238 (c : Candidate) : assignment c 238 = (v238 c) := rfl
theorem assignment_239 (c : Candidate) : assignment c 239 = (v239 c) := rfl
theorem assignment_240 (c : Candidate) : assignment c 240 = (v240 c) := rfl
theorem assignment_241 (c : Candidate) : assignment c 241 = (v241 c) := rfl
theorem assignment_242 (c : Candidate) : assignment c 242 = (v242 c) := rfl
theorem assignment_243 (c : Candidate) : assignment c 243 = (v243 c) := rfl
theorem assignment_244 (c : Candidate) : assignment c 244 = (v244 c) := rfl
theorem assignment_245 (c : Candidate) : assignment c 245 = (v245 c) := rfl
theorem assignment_246 (c : Candidate) : assignment c 246 = (v246 c) := rfl
theorem assignment_247 (c : Candidate) : assignment c 247 = (v247 c) := rfl
theorem assignment_248 (c : Candidate) : assignment c 248 = (v248 c) := rfl
theorem assignment_249 (c : Candidate) : assignment c 249 = (v249 c) := rfl
theorem assignment_250 (c : Candidate) : assignment c 250 = (v250 c) := rfl
theorem assignment_251 (c : Candidate) : assignment c 251 = (v251 c) := rfl
theorem assignment_252 (c : Candidate) : assignment c 252 = (v252 c) := rfl
theorem assignment_253 (c : Candidate) : assignment c 253 = (v253 c) := rfl
theorem assignment_254 (c : Candidate) : assignment c 254 = (v254 c) := rfl
theorem assignment_255 (c : Candidate) : assignment c 255 = (v255 c) := rfl
theorem assignment_256 (c : Candidate) : assignment c 256 = (v256 c) := rfl
theorem assignment_257 (c : Candidate) : assignment c 257 = (v257 c) := rfl
theorem assignment_258 (c : Candidate) : assignment c 258 = (v258 c) := rfl
theorem assignment_259 (c : Candidate) : assignment c 259 = (v259 c) := rfl
theorem assignment_260 (c : Candidate) : assignment c 260 = (v260 c) := rfl
theorem assignment_261 (c : Candidate) : assignment c 261 = (v261 c) := rfl
theorem assignment_262 (c : Candidate) : assignment c 262 = (v262 c) := rfl
theorem assignment_263 (c : Candidate) : assignment c 263 = (v263 c) := rfl
theorem assignment_264 (c : Candidate) : assignment c 264 = (v264 c) := rfl
theorem assignment_265 (c : Candidate) : assignment c 265 = (v265 c) := rfl
theorem assignment_266 (c : Candidate) : assignment c 266 = (v266 c) := rfl
theorem assignment_267 (c : Candidate) : assignment c 267 = (v267 c) := rfl
theorem assignment_268 (c : Candidate) : assignment c 268 = (v268 c) := rfl
theorem assignment_269 (c : Candidate) : assignment c 269 = (v269 c) := rfl
theorem assignment_270 (c : Candidate) : assignment c 270 = (v270 c) := rfl
theorem assignment_271 (c : Candidate) : assignment c 271 = (v271 c) := rfl
theorem assignment_272 (c : Candidate) : assignment c 272 = (v272 c) := rfl
theorem assignment_273 (c : Candidate) : assignment c 273 = (v273 c) := rfl
theorem assignment_274 (c : Candidate) : assignment c 274 = (v274 c) := rfl
theorem assignment_275 (c : Candidate) : assignment c 275 = (v275 c) := rfl
theorem assignment_276 (c : Candidate) : assignment c 276 = (v276 c) := rfl
theorem assignment_277 (c : Candidate) : assignment c 277 = (v277 c) := rfl
theorem assignment_278 (c : Candidate) : assignment c 278 = (v278 c) := rfl
theorem assignment_279 (c : Candidate) : assignment c 279 = (v279 c) := rfl
theorem assignment_280 (c : Candidate) : assignment c 280 = (v280 c) := rfl
theorem assignment_281 (c : Candidate) : assignment c 281 = (v281 c) := rfl
theorem assignment_282 (c : Candidate) : assignment c 282 = (v282 c) := rfl
theorem assignment_283 (c : Candidate) : assignment c 283 = (v283 c) := rfl
theorem assignment_284 (c : Candidate) : assignment c 284 = (v284 c) := rfl
theorem assignment_285 (c : Candidate) : assignment c 285 = (v285 c) := rfl
theorem assignment_286 (c : Candidate) : assignment c 286 = (v286 c) := rfl
theorem assignment_287 (c : Candidate) : assignment c 287 = (v287 c) := rfl
theorem assignment_288 (c : Candidate) : assignment c 288 = (v288 c) := rfl
theorem assignment_289 (c : Candidate) : assignment c 289 = (v289 c) := rfl
theorem assignment_290 (c : Candidate) : assignment c 290 = (v290 c) := rfl
theorem assignment_291 (c : Candidate) : assignment c 291 = (v291 c) := rfl
theorem assignment_292 (c : Candidate) : assignment c 292 = (v292 c) := rfl
theorem assignment_293 (c : Candidate) : assignment c 293 = (v293 c) := rfl
theorem assignment_294 (c : Candidate) : assignment c 294 = (v294 c) := rfl
theorem assignment_295 (c : Candidate) : assignment c 295 = (v295 c) := rfl
theorem assignment_296 (c : Candidate) : assignment c 296 = (v296 c) := rfl
theorem assignment_297 (c : Candidate) : assignment c 297 = (v297 c) := rfl
theorem assignment_298 (c : Candidate) : assignment c 298 = (v298 c) := rfl
theorem assignment_299 (c : Candidate) : assignment c 299 = (v299 c) := rfl
theorem assignment_300 (c : Candidate) : assignment c 300 = (v300 c) := rfl
theorem assignment_301 (c : Candidate) : assignment c 301 = (v301 c) := rfl
theorem assignment_302 (c : Candidate) : assignment c 302 = (v302 c) := rfl
theorem assignment_303 (c : Candidate) : assignment c 303 = (v303 c) := rfl
theorem assignment_304 (c : Candidate) : assignment c 304 = (v304 c) := rfl
theorem assignment_305 (c : Candidate) : assignment c 305 = (v305 c) := rfl
theorem assignment_306 (c : Candidate) : assignment c 306 = (v306 c) := rfl
theorem assignment_307 (c : Candidate) : assignment c 307 = (v307 c) := rfl
theorem assignment_308 (c : Candidate) : assignment c 308 = (v308 c) := rfl
theorem assignment_309 (c : Candidate) : assignment c 309 = (v309 c) := rfl
theorem assignment_310 (c : Candidate) : assignment c 310 = (v310 c) := rfl
theorem assignment_311 (c : Candidate) : assignment c 311 = (v311 c) := rfl
theorem assignment_312 (c : Candidate) : assignment c 312 = (v312 c) := rfl
theorem assignment_313 (c : Candidate) : assignment c 313 = (v313 c) := rfl
theorem assignment_314 (c : Candidate) : assignment c 314 = (v314 c) := rfl
theorem assignment_315 (c : Candidate) : assignment c 315 = (v315 c) := rfl
theorem assignment_316 (c : Candidate) : assignment c 316 = (v316 c) := rfl
theorem assignment_317 (c : Candidate) : assignment c 317 = (v317 c) := rfl
theorem assignment_318 (c : Candidate) : assignment c 318 = (v318 c) := rfl
theorem assignment_319 (c : Candidate) : assignment c 319 = (v319 c) := rfl
theorem assignment_320 (c : Candidate) : assignment c 320 = (v320 c) := rfl
theorem assignment_321 (c : Candidate) : assignment c 321 = (v321 c) := rfl
theorem assignment_322 (c : Candidate) : assignment c 322 = (v322 c) := rfl
theorem assignment_323 (c : Candidate) : assignment c 323 = (v323 c) := rfl
theorem assignment_324 (c : Candidate) : assignment c 324 = (v324 c) := rfl
theorem assignment_325 (c : Candidate) : assignment c 325 = (v325 c) := rfl
theorem assignment_326 (c : Candidate) : assignment c 326 = (v326 c) := rfl
theorem assignment_327 (c : Candidate) : assignment c 327 = (v327 c) := rfl
theorem assignment_328 (c : Candidate) : assignment c 328 = (v328 c) := rfl
theorem assignment_329 (c : Candidate) : assignment c 329 = (v329 c) := rfl
theorem assignment_330 (c : Candidate) : assignment c 330 = (v330 c) := rfl
theorem assignment_331 (c : Candidate) : assignment c 331 = (v331 c) := rfl
theorem assignment_332 (c : Candidate) : assignment c 332 = (v332 c) := rfl
theorem assignment_333 (c : Candidate) : assignment c 333 = (v333 c) := rfl
theorem assignment_334 (c : Candidate) : assignment c 334 = (v334 c) := rfl
theorem assignment_335 (c : Candidate) : assignment c 335 = (v335 c) := rfl
theorem assignment_336 (c : Candidate) : assignment c 336 = (v336 c) := rfl
theorem assignment_337 (c : Candidate) : assignment c 337 = (v337 c) := rfl
theorem assignment_338 (c : Candidate) : assignment c 338 = (v338 c) := rfl
theorem assignment_339 (c : Candidate) : assignment c 339 = (v339 c) := rfl
theorem assignment_340 (c : Candidate) : assignment c 340 = (v340 c) := rfl
theorem assignment_341 (c : Candidate) : assignment c 341 = (v341 c) := rfl
theorem assignment_342 (c : Candidate) : assignment c 342 = (v342 c) := rfl
theorem assignment_343 (c : Candidate) : assignment c 343 = (v343 c) := rfl
theorem assignment_344 (c : Candidate) : assignment c 344 = (v344 c) := rfl
theorem assignment_345 (c : Candidate) : assignment c 345 = (v345 c) := rfl
theorem assignment_346 (c : Candidate) : assignment c 346 = (v346 c) := rfl
theorem assignment_347 (c : Candidate) : assignment c 347 = (v347 c) := rfl
theorem assignment_348 (c : Candidate) : assignment c 348 = (v348 c) := rfl
theorem assignment_349 (c : Candidate) : assignment c 349 = (v349 c) := rfl
theorem assignment_350 (c : Candidate) : assignment c 350 = (v350 c) := rfl
theorem assignment_351 (c : Candidate) : assignment c 351 = (v351 c) := rfl
theorem assignment_352 (c : Candidate) : assignment c 352 = (v352 c) := rfl
theorem assignment_353 (c : Candidate) : assignment c 353 = (v353 c) := rfl
theorem assignment_354 (c : Candidate) : assignment c 354 = (v354 c) := rfl
theorem assignment_355 (c : Candidate) : assignment c 355 = (v355 c) := rfl
theorem assignment_356 (c : Candidate) : assignment c 356 = (v356 c) := rfl
theorem assignment_357 (c : Candidate) : assignment c 357 = (v357 c) := rfl
theorem assignment_358 (c : Candidate) : assignment c 358 = (v358 c) := rfl
theorem assignment_359 (c : Candidate) : assignment c 359 = (v359 c) := rfl
theorem assignment_360 (c : Candidate) : assignment c 360 = (v360 c) := rfl
theorem assignment_361 (c : Candidate) : assignment c 361 = (v361 c) := rfl
theorem assignment_362 (c : Candidate) : assignment c 362 = (v362 c) := rfl
theorem assignment_363 (c : Candidate) : assignment c 363 = (v363 c) := rfl
theorem assignment_364 (c : Candidate) : assignment c 364 = (v364 c) := rfl
theorem assignment_365 (c : Candidate) : assignment c 365 = (v365 c) := rfl
theorem assignment_366 (c : Candidate) : assignment c 366 = (v366 c) := rfl
theorem assignment_367 (c : Candidate) : assignment c 367 = (v367 c) := rfl
theorem assignment_368 (c : Candidate) : assignment c 368 = (v368 c) := rfl
theorem assignment_369 (c : Candidate) : assignment c 369 = (v369 c) := rfl
theorem assignment_370 (c : Candidate) : assignment c 370 = (v370 c) := rfl
theorem assignment_371 (c : Candidate) : assignment c 371 = (v371 c) := rfl
theorem assignment_372 (c : Candidate) : assignment c 372 = (v372 c) := rfl
theorem assignment_373 (c : Candidate) : assignment c 373 = (v373 c) := rfl
theorem assignment_374 (c : Candidate) : assignment c 374 = (v374 c) := rfl
theorem assignment_375 (c : Candidate) : assignment c 375 = (v375 c) := rfl
theorem assignment_376 (c : Candidate) : assignment c 376 = (v376 c) := rfl
theorem assignment_377 (c : Candidate) : assignment c 377 = (v377 c) := rfl
theorem assignment_378 (c : Candidate) : assignment c 378 = (v378 c) := rfl
theorem assignment_379 (c : Candidate) : assignment c 379 = (v379 c) := rfl
theorem assignment_380 (c : Candidate) : assignment c 380 = (v380 c) := rfl
theorem assignment_381 (c : Candidate) : assignment c 381 = (v381 c) := rfl
theorem assignment_382 (c : Candidate) : assignment c 382 = (v382 c) := rfl
theorem assignment_383 (c : Candidate) : assignment c 383 = (v383 c) := rfl
theorem assignment_384 (c : Candidate) : assignment c 384 = (v384 c) := rfl
theorem assignment_385 (c : Candidate) : assignment c 385 = (v385 c) := rfl
theorem assignment_386 (c : Candidate) : assignment c 386 = (v386 c) := rfl
theorem assignment_387 (c : Candidate) : assignment c 387 = (v387 c) := rfl
theorem assignment_388 (c : Candidate) : assignment c 388 = (v388 c) := rfl
theorem assignment_389 (c : Candidate) : assignment c 389 = (v389 c) := rfl
theorem assignment_390 (c : Candidate) : assignment c 390 = (v390 c) := rfl
theorem assignment_391 (c : Candidate) : assignment c 391 = (v391 c) := rfl
theorem assignment_392 (c : Candidate) : assignment c 392 = (v392 c) := rfl
theorem assignment_393 (c : Candidate) : assignment c 393 = (v393 c) := rfl
theorem assignment_394 (c : Candidate) : assignment c 394 = (v394 c) := rfl
theorem assignment_395 (c : Candidate) : assignment c 395 = (v395 c) := rfl
theorem assignment_396 (c : Candidate) : assignment c 396 = (v396 c) := rfl
theorem assignment_397 (c : Candidate) : assignment c 397 = (v397 c) := rfl
theorem assignment_398 (c : Candidate) : assignment c 398 = (v398 c) := rfl
theorem assignment_399 (c : Candidate) : assignment c 399 = (v399 c) := rfl
theorem assignment_400 (c : Candidate) : assignment c 400 = (v400 c) := rfl
theorem assignment_401 (c : Candidate) : assignment c 401 = (v401 c) := rfl
theorem assignment_402 (c : Candidate) : assignment c 402 = (v402 c) := rfl
theorem assignment_403 (c : Candidate) : assignment c 403 = (v403 c) := rfl
theorem assignment_404 (c : Candidate) : assignment c 404 = (v404 c) := rfl
theorem assignment_405 (c : Candidate) : assignment c 405 = (v405 c) := rfl
theorem assignment_406 (c : Candidate) : assignment c 406 = (v406 c) := rfl
theorem assignment_407 (c : Candidate) : assignment c 407 = (v407 c) := rfl
theorem assignment_408 (c : Candidate) : assignment c 408 = (v408 c) := rfl
theorem assignment_409 (c : Candidate) : assignment c 409 = (v409 c) := rfl
theorem assignment_410 (c : Candidate) : assignment c 410 = (v410 c) := rfl
theorem assignment_411 (c : Candidate) : assignment c 411 = (v411 c) := rfl
theorem assignment_412 (c : Candidate) : assignment c 412 = (v412 c) := rfl
theorem assignment_413 (c : Candidate) : assignment c 413 = (v413 c) := rfl
theorem assignment_414 (c : Candidate) : assignment c 414 = (v414 c) := rfl
theorem assignment_415 (c : Candidate) : assignment c 415 = (v415 c) := rfl
theorem assignment_416 (c : Candidate) : assignment c 416 = (v416 c) := rfl
theorem assignment_417 (c : Candidate) : assignment c 417 = (v417 c) := rfl
theorem assignment_418 (c : Candidate) : assignment c 418 = (v418 c) := rfl
theorem assignment_419 (c : Candidate) : assignment c 419 = (v419 c) := rfl
theorem assignment_420 (c : Candidate) : assignment c 420 = (v420 c) := rfl
theorem assignment_421 (c : Candidate) : assignment c 421 = (v421 c) := rfl
theorem assignment_422 (c : Candidate) : assignment c 422 = (v422 c) := rfl
theorem assignment_423 (c : Candidate) : assignment c 423 = (v423 c) := rfl
theorem assignment_424 (c : Candidate) : assignment c 424 = (v424 c) := rfl
theorem assignment_425 (c : Candidate) : assignment c 425 = (v425 c) := rfl
theorem assignment_426 (c : Candidate) : assignment c 426 = (v426 c) := rfl
theorem assignment_427 (c : Candidate) : assignment c 427 = (v427 c) := rfl
theorem assignment_428 (c : Candidate) : assignment c 428 = (v428 c) := rfl
theorem assignment_429 (c : Candidate) : assignment c 429 = (v429 c) := rfl
theorem assignment_430 (c : Candidate) : assignment c 430 = (v430 c) := rfl
theorem assignment_431 (c : Candidate) : assignment c 431 = (v431 c) := rfl
theorem assignment_432 (c : Candidate) : assignment c 432 = (v432 c) := rfl
theorem assignment_433 (c : Candidate) : assignment c 433 = (v433 c) := rfl
theorem assignment_434 (c : Candidate) : assignment c 434 = (v434 c) := rfl
theorem assignment_435 (c : Candidate) : assignment c 435 = (v435 c) := rfl
theorem assignment_436 (c : Candidate) : assignment c 436 = (v436 c) := rfl
theorem assignment_437 (c : Candidate) : assignment c 437 = (v437 c) := rfl
theorem assignment_438 (c : Candidate) : assignment c 438 = (v438 c) := rfl
theorem assignment_439 (c : Candidate) : assignment c 439 = (v439 c) := rfl
theorem assignment_440 (c : Candidate) : assignment c 440 = (v440 c) := rfl
theorem assignment_441 (c : Candidate) : assignment c 441 = (v441 c) := rfl
theorem assignment_442 (c : Candidate) : assignment c 442 = (v442 c) := rfl
theorem assignment_443 (c : Candidate) : assignment c 443 = (v443 c) := rfl
theorem assignment_444 (c : Candidate) : assignment c 444 = (v444 c) := rfl
theorem assignment_445 (c : Candidate) : assignment c 445 = (v445 c) := rfl
theorem assignment_446 (c : Candidate) : assignment c 446 = (v446 c) := rfl
theorem assignment_447 (c : Candidate) : assignment c 447 = (v447 c) := rfl
theorem assignment_448 (c : Candidate) : assignment c 448 = (v448 c) := rfl
theorem assignment_449 (c : Candidate) : assignment c 449 = (v449 c) := rfl
theorem assignment_450 (c : Candidate) : assignment c 450 = (v450 c) := rfl
theorem assignment_451 (c : Candidate) : assignment c 451 = (v451 c) := rfl
theorem assignment_452 (c : Candidate) : assignment c 452 = (v452 c) := rfl

def output (c : Candidate) (r : Fin 16) : Bool :=
  ([(v129 c), (v144 c), (v159 c), (v174 c), (v189 c), (v204 c), (v219 c), (v234 c), (v249 c), (v264 c), (v279 c), (v294 c), (v309 c), (v324 c), (v339 c), (v352 c)] : List Bool).getD r.val false

def target (r : Fin 16) : Bool :=
  (r.val.testBit 0 && r.val.testBit 1) || (r.val.testBit 0 && r.val.testBit 2) || (r.val.testBit 1 && r.val.testBit 3)

def derivativeLeft (c : Candidate) : Bool := (v402 c)
def derivativeRight (c : Candidate) : Bool := (v452 c)

example (c : Candidate) (hv : valid c)
    (hr : ∀ r : Fin 16, output c r = target r)
    (hl : derivativeLeft c = false) (hd : derivativeRight c = false) : True := by
  rcases hv with ⟨h0, h1, h2, h3, h4⟩
  have hc0 : ClauseSat (assignment c) [2] := by
    simp [ClauseSat, litVal, assignment_1]
  have hc1 : ClauseSat (assignment c) [6,8,10,12] := by
    have hb := c.a0.isLt
    simp [ClauseSat, litVal, assignment_3, assignment_4, assignment_5, assignment_6, v3, v4, v5, v6]
    omega
  have hc2 : ClauseSat (assignment c) [7,9] := by
    simp [ClauseSat, litVal, assignment_3, assignment_4, v3, v4]
    all_goals omega
  have hc3 : ClauseSat (assignment c) [23,7] := by
    cases ha0 : v3 c <;> cases ha1 : v4 c <;> simp [ClauseSat, litVal, assignment_3, assignment_11, v11, ha0, ha1]
  have hc4 : ClauseSat (assignment c) [23,9] := by
    cases ha0 : v3 c <;> cases ha1 : v4 c <;> simp [ClauseSat, litVal, assignment_4, assignment_11, v11, ha0, ha1]
  have hc5 : ClauseSat (assignment c) [22,6,8] := by
    cases ha0 : v3 c <;> cases ha1 : v4 c <;> simp [ClauseSat, litVal, assignment_3, assignment_4, assignment_11, v11, ha0, ha1]
  have hc6 : ClauseSat (assignment c) [22,11] := by
    simp [ClauseSat, litVal, assignment_5, assignment_11, v3, v4, v5, v11]
    all_goals omega
  have hc7 : ClauseSat (assignment c) [25,22] := by
    cases ha0 : v5 c <;> cases ha1 : v11 c <;> simp [ClauseSat, litVal, assignment_11, assignment_12, v12, ha0, ha1]
  have hc8 : ClauseSat (assignment c) [25,11] := by
    cases ha0 : v5 c <;> cases ha1 : v11 c <;> simp [ClauseSat, litVal, assignment_5, assignment_12, v12, ha0, ha1]
  have hc9 : ClauseSat (assignment c) [24,23,10] := by
    cases ha0 : v5 c <;> cases ha1 : v11 c <;> simp [ClauseSat, litVal, assignment_5, assignment_11, assignment_12, v12, ha0, ha1]
  have hc10 : ClauseSat (assignment c) [24,13] := by
    simp [ClauseSat, litVal, assignment_6, assignment_12, v3, v4, v5, v6, v11, v12]
    all_goals omega
  have hc11 : ClauseSat (assignment c) [27,24] := by
    cases ha0 : v6 c <;> cases ha1 : v12 c <;> simp [ClauseSat, litVal, assignment_12, assignment_13, v13, ha0, ha1]
  have hc12 : ClauseSat (assignment c) [27,13] := by
    cases ha0 : v6 c <;> cases ha1 : v12 c <;> simp [ClauseSat, litVal, assignment_6, assignment_13, v13, ha0, ha1]
  have hc13 : ClauseSat (assignment c) [26,25,12] := by
    cases ha0 : v6 c <;> cases ha1 : v12 c <;> simp [ClauseSat, litVal, assignment_6, assignment_12, assignment_13, v13, ha0, ha1]
  have hc14 : ClauseSat (assignment c) [14,16,18,20] := by
    have hb := c.b0.isLt
    simp [ClauseSat, litVal, assignment_7, assignment_8, assignment_9, assignment_10, v7, v8, v9, v10]
    omega
  have hc15 : ClauseSat (assignment c) [15,17] := by
    simp [ClauseSat, litVal, assignment_7, assignment_8, v7, v8]
    all_goals omega
  have hc16 : ClauseSat (assignment c) [29,15] := by
    cases ha0 : v7 c <;> cases ha1 : v8 c <;> simp [ClauseSat, litVal, assignment_7, assignment_14, v14, ha0, ha1]
  have hc17 : ClauseSat (assignment c) [29,17] := by
    cases ha0 : v7 c <;> cases ha1 : v8 c <;> simp [ClauseSat, litVal, assignment_8, assignment_14, v14, ha0, ha1]
  have hc18 : ClauseSat (assignment c) [28,14,16] := by
    cases ha0 : v7 c <;> cases ha1 : v8 c <;> simp [ClauseSat, litVal, assignment_7, assignment_8, assignment_14, v14, ha0, ha1]
  have hc19 : ClauseSat (assignment c) [28,19] := by
    simp [ClauseSat, litVal, assignment_9, assignment_14, v7, v8, v9, v14]
    all_goals omega
  have hc20 : ClauseSat (assignment c) [31,28] := by
    cases ha0 : v9 c <;> cases ha1 : v14 c <;> simp [ClauseSat, litVal, assignment_14, assignment_15, v15, ha0, ha1]
  have hc21 : ClauseSat (assignment c) [31,19] := by
    cases ha0 : v9 c <;> cases ha1 : v14 c <;> simp [ClauseSat, litVal, assignment_9, assignment_15, v15, ha0, ha1]
  have hc22 : ClauseSat (assignment c) [30,29,18] := by
    cases ha0 : v9 c <;> cases ha1 : v14 c <;> simp [ClauseSat, litVal, assignment_9, assignment_14, assignment_15, v15, ha0, ha1]
  have hc23 : ClauseSat (assignment c) [30,21] := by
    simp [ClauseSat, litVal, assignment_10, assignment_15, v7, v8, v9, v10, v14, v15]
    all_goals omega
  have hc24 : ClauseSat (assignment c) [33,30] := by
    cases ha0 : v10 c <;> cases ha1 : v15 c <;> simp [ClauseSat, litVal, assignment_15, assignment_16, v16, ha0, ha1]
  have hc25 : ClauseSat (assignment c) [33,21] := by
    cases ha0 : v10 c <;> cases ha1 : v15 c <;> simp [ClauseSat, litVal, assignment_10, assignment_16, v16, ha0, ha1]
  have hc26 : ClauseSat (assignment c) [32,31,20] := by
    cases ha0 : v10 c <;> cases ha1 : v15 c <;> simp [ClauseSat, litVal, assignment_10, assignment_15, assignment_16, v16, ha0, ha1]
  have hc27 : ClauseSat (assignment c) [7,15] := by
    simp [ClauseSat, litVal, assignment_3, assignment_7, v3, v7]
    all_goals omega
  have hc28 : ClauseSat (assignment c) [9,28] := by
    simp [ClauseSat, litVal, assignment_4, assignment_14, v4, v7, v8, v14]
    all_goals omega
  have hc29 : ClauseSat (assignment c) [11,30] := by
    simp [ClauseSat, litVal, assignment_5, assignment_15, v5, v7, v8, v9, v14, v15]
    all_goals omega
  trivial

end PEqualNP.Outside.Pilot64Bridge
