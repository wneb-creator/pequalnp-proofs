import Mathlib.Tactic

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem PEqualNP.Outside.L_meta_2602_aux.rup_unsat (p : Nat → Prop)
    (c1 : (¬ p 26) → (p 0) → False)
    (c2 : (¬ p 26) → (p 1) → False)
    (c3 : (p 26) → (¬ p 0) → (¬ p 1) → False)
    (c4 : (¬ p 27) → (p 26) → False)
    (c5 : (¬ p 27) → (p 3) → False)
    (c6 : (p 27) → (¬ p 26) → (¬ p 3) → False)
    (c7 : (¬ p 28) → (p 27) → False)
    (c8 : (¬ p 28) → (p 9) → False)
    (c9 : (p 28) → (¬ p 27) → (¬ p 9) → False)
    (c10 : (p 29) → (¬ p 13) → False)
    (c11 : (p 29) → (¬ p 28) → False)
    (c12 : (¬ p 29) → (p 13) → (p 28) → False)
    (c13 : (¬ p 30) → (p 2) → False)
    (c14 : (¬ p 30) → (p 3) → False)
    (c15 : (p 30) → (¬ p 2) → (¬ p 3) → False)
    (c16 : (¬ p 31) → (p 30) → False)
    (c17 : (¬ p 31) → (p 5) → False)
    (c18 : (p 31) → (¬ p 30) → (¬ p 5) → False)
    (c19 : (¬ p 32) → (p 31) → False)
    (c20 : (¬ p 32) → (p 11) → False)
    (c21 : (p 32) → (¬ p 31) → (¬ p 11) → False)
    (c22 : (p 33) → (¬ p 15) → False)
    (c23 : (p 33) → (¬ p 32) → False)
    (c24 : (¬ p 33) → (p 15) → (p 32) → False)
    (c25 : (¬ p 34) → (p 3) → False)
    (c26 : (¬ p 34) → (p 4) → False)
    (c27 : (p 34) → (¬ p 3) → (¬ p 4) → False)
    (c28 : (¬ p 35) → (p 34) → False)
    (c29 : (¬ p 35) → (p 6) → False)
    (c30 : (p 35) → (¬ p 34) → (¬ p 6) → False)
    (c31 : (¬ p 36) → (p 35) → False)
    (c32 : (¬ p 36) → (p 12) → False)
    (c33 : (p 36) → (¬ p 35) → (¬ p 12) → False)
    (c34 : (p 37) → (¬ p 16) → False)
    (c35 : (p 37) → (¬ p 36) → False)
    (c36 : (¬ p 37) → (p 16) → (p 36) → False)
    (c37 : (¬ p 38) → (p 4) → False)
    (c38 : (¬ p 38) → (p 5) → False)
    (c39 : (p 38) → (¬ p 4) → (¬ p 5) → False)
    (c40 : (¬ p 39) → (p 38) → False)
    (c41 : (¬ p 39) → (p 7) → False)
    (c42 : (p 39) → (¬ p 38) → (¬ p 7) → False)
    (c43 : (¬ p 40) → (p 39) → False)
    (c44 : (¬ p 40) → (p 0) → False)
    (c45 : (p 40) → (¬ p 39) → (¬ p 0) → False)
    (c46 : (p 41) → (¬ p 17) → False)
    (c47 : (p 41) → (¬ p 40) → False)
    (c48 : (¬ p 41) → (p 17) → (p 40) → False)
    (c49 : (¬ p 42) → (p 5) → False)
    (c50 : (¬ p 42) → (p 6) → False)
    (c51 : (p 42) → (¬ p 5) → (¬ p 6) → False)
    (c52 : (¬ p 43) → (p 42) → False)
    (c53 : (¬ p 43) → (p 8) → False)
    (c54 : (p 43) → (¬ p 42) → (¬ p 8) → False)
    (c55 : (¬ p 44) → (p 43) → False)
    (c56 : (¬ p 44) → (p 1) → False)
    (c57 : (p 44) → (¬ p 43) → (¬ p 1) → False)
    (c58 : (p 45) → (¬ p 18) → False)
    (c59 : (p 45) → (¬ p 44) → False)
    (c60 : (¬ p 45) → (p 18) → (p 44) → False)
    (c61 : (¬ p 46) → (p 6) → False)
    (c62 : (¬ p 46) → (p 7) → False)
    (c63 : (p 46) → (¬ p 6) → (¬ p 7) → False)
    (c64 : (¬ p 47) → (p 46) → False)
    (c65 : (¬ p 47) → (p 9) → False)
    (c66 : (p 47) → (¬ p 46) → (¬ p 9) → False)
    (c67 : (¬ p 48) → (p 47) → False)
    (c68 : (¬ p 48) → (p 2) → False)
    (c69 : (p 48) → (¬ p 47) → (¬ p 2) → False)
    (c70 : (p 49) → (¬ p 19) → False)
    (c71 : (p 49) → (¬ p 48) → False)
    (c72 : (¬ p 49) → (p 19) → (p 48) → False)
    (c73 : (¬ p 50) → (p 7) → False)
    (c74 : (¬ p 50) → (p 8) → False)
    (c75 : (p 50) → (¬ p 7) → (¬ p 8) → False)
    (c76 : (¬ p 51) → (p 50) → False)
    (c77 : (¬ p 51) → (p 10) → False)
    (c78 : (p 51) → (¬ p 50) → (¬ p 10) → False)
    (c79 : (¬ p 52) → (p 51) → False)
    (c80 : (¬ p 52) → (p 3) → False)
    (c81 : (p 52) → (¬ p 51) → (¬ p 3) → False)
    (c82 : (p 53) → (¬ p 20) → False)
    (c83 : (p 53) → (¬ p 52) → False)
    (c84 : (¬ p 53) → (p 20) → (p 52) → False)
    (c85 : (¬ p 54) → (p 8) → False)
    (c86 : (¬ p 54) → (p 9) → False)
    (c87 : (p 54) → (¬ p 8) → (¬ p 9) → False)
    (c88 : (¬ p 55) → (p 54) → False)
    (c89 : (¬ p 55) → (p 11) → False)
    (c90 : (p 55) → (¬ p 54) → (¬ p 11) → False)
    (c91 : (¬ p 56) → (p 55) → False)
    (c92 : (¬ p 56) → (p 4) → False)
    (c93 : (p 56) → (¬ p 55) → (¬ p 4) → False)
    (c94 : (p 57) → (¬ p 21) → False)
    (c95 : (p 57) → (¬ p 56) → False)
    (c96 : (¬ p 57) → (p 21) → (p 56) → False)
    (c97 : (¬ p 58) → (p 9) → False)
    (c98 : (¬ p 58) → (p 10) → False)
    (c99 : (p 58) → (¬ p 9) → (¬ p 10) → False)
    (c100 : (¬ p 59) → (p 58) → False)
    (c101 : (¬ p 59) → (p 12) → False)
    (c102 : (p 59) → (¬ p 58) → (¬ p 12) → False)
    (c103 : (¬ p 60) → (p 59) → False)
    (c104 : (¬ p 60) → (p 5) → False)
    (c105 : (p 60) → (¬ p 59) → (¬ p 5) → False)
    (c106 : (p 61) → (¬ p 22) → False)
    (c107 : (p 61) → (¬ p 60) → False)
    (c108 : (¬ p 61) → (p 22) → (p 60) → False)
    (c109 : (¬ p 62) → (p 10) → False)
    (c110 : (¬ p 62) → (p 11) → False)
    (c111 : (p 62) → (¬ p 10) → (¬ p 11) → False)
    (c112 : (¬ p 63) → (p 62) → False)
    (c113 : (¬ p 63) → (p 0) → False)
    (c114 : (p 63) → (¬ p 62) → (¬ p 0) → False)
    (c115 : (¬ p 64) → (p 63) → False)
    (c116 : (¬ p 64) → (p 6) → False)
    (c117 : (p 64) → (¬ p 63) → (¬ p 6) → False)
    (c118 : (p 65) → (¬ p 23) → False)
    (c119 : (p 65) → (¬ p 64) → False)
    (c120 : (¬ p 65) → (p 23) → (p 64) → False)
    (c121 : (¬ p 66) → (p 11) → False)
    (c122 : (¬ p 66) → (p 12) → False)
    (c123 : (p 66) → (¬ p 11) → (¬ p 12) → False)
    (c124 : (¬ p 67) → (p 66) → False)
    (c125 : (¬ p 67) → (p 1) → False)
    (c126 : (p 67) → (¬ p 66) → (¬ p 1) → False)
    (c127 : (¬ p 68) → (p 67) → False)
    (c128 : (¬ p 68) → (p 7) → False)
    (c129 : (p 68) → (¬ p 67) → (¬ p 7) → False)
    (c130 : (p 69) → (¬ p 24) → False)
    (c131 : (p 69) → (¬ p 68) → False)
    (c132 : (¬ p 69) → (p 24) → (p 68) → False)
    (c133 : (¬ p 70) → (p 12) → False)
    (c134 : (¬ p 70) → (p 0) → False)
    (c135 : (p 70) → (¬ p 12) → (¬ p 0) → False)
    (c136 : (¬ p 71) → (p 70) → False)
    (c137 : (¬ p 71) → (p 2) → False)
    (c138 : (p 71) → (¬ p 70) → (¬ p 2) → False)
    (c139 : (¬ p 72) → (p 71) → False)
    (c140 : (¬ p 72) → (p 8) → False)
    (c141 : (p 72) → (¬ p 71) → (¬ p 8) → False)
    (c142 : (p 73) → (¬ p 25) → False)
    (c143 : (p 73) → (¬ p 72) → False)
    (c144 : (¬ p 73) → (p 25) → (p 72) → False)
    (c145 : (¬ p 74) → (p 29) → False)
    (c146 : (¬ p 74) → (p 33) → False)
    (c147 : (p 74) → (¬ p 29) → (¬ p 33) → False)
    (c148 : (¬ p 75) → (p 74) → False)
    (c149 : (¬ p 75) → (p 37) → False)
    (c150 : (p 75) → (¬ p 74) → (¬ p 37) → False)
    (c151 : (¬ p 76) → (p 75) → False)
    (c152 : (¬ p 76) → (p 41) → False)
    (c153 : (p 76) → (¬ p 75) → (¬ p 41) → False)
    (c154 : (¬ p 77) → (p 76) → False)
    (c155 : (¬ p 77) → (p 45) → False)
    (c156 : (p 77) → (¬ p 76) → (¬ p 45) → False)
    (c157 : (¬ p 78) → (p 77) → False)
    (c158 : (¬ p 78) → (p 49) → False)
    (c159 : (p 78) → (¬ p 77) → (¬ p 49) → False)
    (c160 : (¬ p 79) → (p 78) → False)
    (c161 : (¬ p 79) → (p 53) → False)
    (c162 : (p 79) → (¬ p 78) → (¬ p 53) → False)
    (c163 : (¬ p 80) → (p 79) → False)
    (c164 : (¬ p 80) → (p 57) → False)
    (c165 : (p 80) → (¬ p 79) → (¬ p 57) → False)
    (c166 : (¬ p 81) → (p 80) → False)
    (c167 : (¬ p 81) → (p 61) → False)
    (c168 : (p 81) → (¬ p 80) → (¬ p 61) → False)
    (c169 : (¬ p 82) → (p 81) → False)
    (c170 : (¬ p 82) → (p 65) → False)
    (c171 : (p 82) → (¬ p 81) → (¬ p 65) → False)
    (c172 : (¬ p 83) → (p 82) → False)
    (c173 : (¬ p 83) → (p 69) → False)
    (c174 : (p 83) → (¬ p 82) → (¬ p 69) → False)
    (c175 : (¬ p 84) → (p 83) → False)
    (c176 : (¬ p 84) → (p 73) → False)
    (c177 : (p 84) → (¬ p 83) → (¬ p 73) → False)
    (c178 : (¬ p 85) → (p 84) → False)
    (c179 : (¬ p 85) → (p 1) → False)
    (c180 : (p 85) → (¬ p 84) → (¬ p 1) → False)
    (c181 : (¬ p 86) → (p 85) → False)
    (c182 : (¬ p 86) → (p 2) → False)
    (c183 : (p 86) → (¬ p 85) → (¬ p 2) → False)
    (c184 : (¬ p 87) → (p 86) → False)
    (c185 : (¬ p 87) → (p 4) → False)
    (c186 : (p 87) → (¬ p 86) → (¬ p 4) → False)
    (c187 : (¬ p 88) → (p 87) → False)
    (c188 : (¬ p 88) → (p 10) → False)
    (c189 : (p 88) → (¬ p 87) → (¬ p 10) → False)
    (c190 : (¬ p 89) → (p 84) → False)
    (c191 : (¬ p 89) → (p 14) → False)
    (c192 : (p 89) → (¬ p 84) → (¬ p 14) → False)
    (c193 : (p 90) → (¬ p 88) → False)
    (c194 : (p 90) → (¬ p 89) → False)
    (c195 : (¬ p 90) → (p 88) → (p 89) → False)
    (c196 : (p 91) → (¬ p 0) → False)
    (c197 : (p 91) → (¬ p 13) → False)
    (c198 : (¬ p 91) → (p 0) → (p 13) → False)
    (c199 : (p 92) → (¬ p 0) → False)
    (c200 : (p 92) → (¬ p 17) → False)
    (c201 : (¬ p 92) → (p 0) → (p 17) → False)
    (c202 : (p 93) → (¬ p 0) → False)
    (c203 : (p 93) → (¬ p 23) → False)
    (c204 : (¬ p 93) → (p 0) → (p 23) → False)
    (c205 : (p 94) → (¬ p 0) → False)
    (c206 : (p 94) → (¬ p 25) → False)
    (c207 : (¬ p 94) → (p 0) → (p 25) → False)
    (c208 : (p 95) → (¬ p 1) → False)
    (c209 : (p 95) → (¬ p 13) → False)
    (c210 : (¬ p 95) → (p 1) → (p 13) → False)
    (c211 : (p 96) → (¬ p 1) → False)
    (c212 : (p 96) → (¬ p 14) → False)
    (c213 : (¬ p 96) → (p 1) → (p 14) → False)
    (c214 : (p 97) → (¬ p 1) → False)
    (c215 : (p 97) → (¬ p 18) → False)
    (c216 : (¬ p 97) → (p 1) → (p 18) → False)
    (c217 : (p 98) → (¬ p 1) → False)
    (c218 : (p 98) → (¬ p 24) → False)
    (c219 : (¬ p 98) → (p 1) → (p 24) → False)
    (c220 : (p 99) → (¬ p 2) → False)
    (c221 : (p 99) → (¬ p 14) → False)
    (c222 : (¬ p 99) → (p 2) → (p 14) → False)
    (c223 : (p 100) → (¬ p 2) → False)
    (c224 : (p 100) → (¬ p 15) → False)
    (c225 : (¬ p 100) → (p 2) → (p 15) → False)
    (c226 : (p 101) → (¬ p 2) → False)
    (c227 : (p 101) → (¬ p 19) → False)
    (c228 : (¬ p 101) → (p 2) → (p 19) → False)
    (c229 : (p 102) → (¬ p 2) → False)
    (c230 : (p 102) → (¬ p 25) → False)
    (c231 : (¬ p 102) → (p 2) → (p 25) → False)
    (c232 : (p 103) → (¬ p 3) → False)
    (c233 : (p 103) → (¬ p 13) → False)
    (c234 : (¬ p 103) → (p 3) → (p 13) → False)
    (c235 : (p 104) → (¬ p 3) → False)
    (c236 : (p 104) → (¬ p 15) → False)
    (c237 : (¬ p 104) → (p 3) → (p 15) → False)
    (c238 : (p 105) → (¬ p 3) → False)
    (c239 : (p 105) → (¬ p 16) → False)
    (c240 : (¬ p 105) → (p 3) → (p 16) → False)
    (c241 : (p 106) → (¬ p 3) → False)
    (c242 : (p 106) → (¬ p 20) → False)
    (c243 : (¬ p 106) → (p 3) → (p 20) → False)
    (c244 : (p 107) → (¬ p 4) → False)
    (c245 : (p 107) → (¬ p 14) → False)
    (c246 : (¬ p 107) → (p 4) → (p 14) → False)
    (c247 : (p 108) → (¬ p 4) → False)
    (c248 : (p 108) → (¬ p 16) → False)
    (c249 : (¬ p 108) → (p 4) → (p 16) → False)
    (c250 : (p 109) → (¬ p 4) → False)
    (c251 : (p 109) → (¬ p 17) → False)
    (c252 : (¬ p 109) → (p 4) → (p 17) → False)
    (c253 : (p 110) → (¬ p 4) → False)
    (c254 : (p 110) → (¬ p 21) → False)
    (c255 : (¬ p 110) → (p 4) → (p 21) → False)
    (c256 : (p 111) → (¬ p 5) → False)
    (c257 : (p 111) → (¬ p 15) → False)
    (c258 : (¬ p 111) → (p 5) → (p 15) → False)
    (c259 : (p 112) → (¬ p 5) → False)
    (c260 : (p 112) → (¬ p 17) → False)
    (c261 : (¬ p 112) → (p 5) → (p 17) → False)
    (c262 : (p 113) → (¬ p 5) → False)
    (c263 : (p 113) → (¬ p 18) → False)
    (c264 : (¬ p 113) → (p 5) → (p 18) → False)
    (c265 : (p 114) → (¬ p 5) → False)
    (c266 : (p 114) → (¬ p 22) → False)
    (c267 : (¬ p 114) → (p 5) → (p 22) → False)
    (c268 : (p 115) → (¬ p 6) → False)
    (c269 : (p 115) → (¬ p 16) → False)
    (c270 : (¬ p 115) → (p 6) → (p 16) → False)
    (c271 : (p 116) → (¬ p 6) → False)
    (c272 : (p 116) → (¬ p 18) → False)
    (c273 : (¬ p 116) → (p 6) → (p 18) → False)
    (c274 : (p 117) → (¬ p 6) → False)
    (c275 : (p 117) → (¬ p 19) → False)
    (c276 : (¬ p 117) → (p 6) → (p 19) → False)
    (c277 : (p 118) → (¬ p 6) → False)
    (c278 : (p 118) → (¬ p 23) → False)
    (c279 : (¬ p 118) → (p 6) → (p 23) → False)
    (c280 : (p 119) → (¬ p 7) → False)
    (c281 : (p 119) → (¬ p 17) → False)
    (c282 : (¬ p 119) → (p 7) → (p 17) → False)
    (c283 : (p 120) → (¬ p 7) → False)
    (c284 : (p 120) → (¬ p 19) → False)
    (c285 : (¬ p 120) → (p 7) → (p 19) → False)
    (c286 : (p 121) → (¬ p 7) → False)
    (c287 : (p 121) → (¬ p 20) → False)
    (c288 : (¬ p 121) → (p 7) → (p 20) → False)
    (c289 : (p 122) → (¬ p 7) → False)
    (c290 : (p 122) → (¬ p 24) → False)
    (c291 : (¬ p 122) → (p 7) → (p 24) → False)
    (c292 : (p 123) → (¬ p 8) → False)
    (c293 : (p 123) → (¬ p 18) → False)
    (c294 : (¬ p 123) → (p 8) → (p 18) → False)
    (c295 : (p 124) → (¬ p 8) → False)
    (c296 : (p 124) → (¬ p 20) → False)
    (c297 : (¬ p 124) → (p 8) → (p 20) → False)
    (c298 : (p 125) → (¬ p 8) → False)
    (c299 : (p 125) → (¬ p 21) → False)
    (c300 : (¬ p 125) → (p 8) → (p 21) → False)
    (c301 : (p 126) → (¬ p 8) → False)
    (c302 : (p 126) → (¬ p 25) → False)
    (c303 : (¬ p 126) → (p 8) → (p 25) → False)
    (c304 : (p 127) → (¬ p 9) → False)
    (c305 : (p 127) → (¬ p 13) → False)
    (c306 : (¬ p 127) → (p 9) → (p 13) → False)
    (c307 : (p 128) → (¬ p 9) → False)
    (c308 : (p 128) → (¬ p 19) → False)
    (c309 : (¬ p 128) → (p 9) → (p 19) → False)
    (c310 : (p 129) → (¬ p 9) → False)
    (c311 : (p 129) → (¬ p 21) → False)
    (c312 : (¬ p 129) → (p 9) → (p 21) → False)
    (c313 : (p 130) → (¬ p 9) → False)
    (c314 : (p 130) → (¬ p 22) → False)
    (c315 : (¬ p 130) → (p 9) → (p 22) → False)
    (c316 : (p 131) → (¬ p 10) → False)
    (c317 : (p 131) → (¬ p 14) → False)
    (c318 : (¬ p 131) → (p 10) → (p 14) → False)
    (c319 : (p 132) → (¬ p 10) → False)
    (c320 : (p 132) → (¬ p 20) → False)
    (c321 : (¬ p 132) → (p 10) → (p 20) → False)
    (c322 : (p 133) → (¬ p 10) → False)
    (c323 : (p 133) → (¬ p 22) → False)
    (c324 : (¬ p 133) → (p 10) → (p 22) → False)
    (c325 : (p 134) → (¬ p 10) → False)
    (c326 : (p 134) → (¬ p 23) → False)
    (c327 : (¬ p 134) → (p 10) → (p 23) → False)
    (c328 : (p 135) → (¬ p 11) → False)
    (c329 : (p 135) → (¬ p 15) → False)
    (c330 : (¬ p 135) → (p 11) → (p 15) → False)
    (c331 : (p 136) → (¬ p 11) → False)
    (c332 : (p 136) → (¬ p 21) → False)
    (c333 : (¬ p 136) → (p 11) → (p 21) → False)
    (c334 : (p 137) → (¬ p 11) → False)
    (c335 : (p 137) → (¬ p 23) → False)
    (c336 : (¬ p 137) → (p 11) → (p 23) → False)
    (c337 : (p 138) → (¬ p 11) → False)
    (c338 : (p 138) → (¬ p 24) → False)
    (c339 : (¬ p 138) → (p 11) → (p 24) → False)
    (c340 : (p 139) → (¬ p 12) → False)
    (c341 : (p 139) → (¬ p 16) → False)
    (c342 : (¬ p 139) → (p 12) → (p 16) → False)
    (c343 : (p 140) → (¬ p 12) → False)
    (c344 : (p 140) → (¬ p 22) → False)
    (c345 : (¬ p 140) → (p 12) → (p 22) → False)
    (c346 : (p 141) → (¬ p 12) → False)
    (c347 : (p 141) → (¬ p 24) → False)
    (c348 : (¬ p 141) → (p 12) → (p 24) → False)
    (c349 : (p 142) → (¬ p 12) → False)
    (c350 : (p 142) → (¬ p 25) → False)
    (c351 : (¬ p 142) → (p 12) → (p 25) → False)
    (c352 : (¬ p 143) → (p 91) → False)
    (c353 : (¬ p 143) → (p 92) → False)
    (c354 : (p 143) → (¬ p 91) → (¬ p 92) → False)
    (c355 : (¬ p 144) → (p 143) → False)
    (c356 : (¬ p 144) → (p 93) → False)
    (c357 : (p 144) → (¬ p 143) → (¬ p 93) → False)
    (c358 : (¬ p 145) → (p 144) → False)
    (c359 : (¬ p 145) → (p 94) → False)
    (c360 : (p 145) → (¬ p 144) → (¬ p 94) → False)
    (c361 : (¬ p 146) → (p 145) → False)
    (c362 : (¬ p 146) → (p 95) → False)
    (c363 : (p 146) → (¬ p 145) → (¬ p 95) → False)
    (c364 : (¬ p 147) → (p 146) → False)
    (c365 : (¬ p 147) → (p 96) → False)
    (c366 : (p 147) → (¬ p 146) → (¬ p 96) → False)
    (c367 : (¬ p 148) → (p 147) → False)
    (c368 : (¬ p 148) → (p 97) → False)
    (c369 : (p 148) → (¬ p 147) → (¬ p 97) → False)
    (c370 : (¬ p 149) → (p 148) → False)
    (c371 : (¬ p 149) → (p 98) → False)
    (c372 : (p 149) → (¬ p 148) → (¬ p 98) → False)
    (c373 : (¬ p 150) → (p 149) → False)
    (c374 : (¬ p 150) → (p 99) → False)
    (c375 : (p 150) → (¬ p 149) → (¬ p 99) → False)
    (c376 : (¬ p 151) → (p 150) → False)
    (c377 : (¬ p 151) → (p 100) → False)
    (c378 : (p 151) → (¬ p 150) → (¬ p 100) → False)
    (c379 : (¬ p 152) → (p 151) → False)
    (c380 : (¬ p 152) → (p 101) → False)
    (c381 : (p 152) → (¬ p 151) → (¬ p 101) → False)
    (c382 : (¬ p 153) → (p 152) → False)
    (c383 : (¬ p 153) → (p 102) → False)
    (c384 : (p 153) → (¬ p 152) → (¬ p 102) → False)
    (c385 : (¬ p 154) → (p 153) → False)
    (c386 : (¬ p 154) → (p 103) → False)
    (c387 : (p 154) → (¬ p 153) → (¬ p 103) → False)
    (c388 : (¬ p 155) → (p 154) → False)
    (c389 : (¬ p 155) → (p 104) → False)
    (c390 : (p 155) → (¬ p 154) → (¬ p 104) → False)
    (c391 : (¬ p 156) → (p 155) → False)
    (c392 : (¬ p 156) → (p 105) → False)
    (c393 : (p 156) → (¬ p 155) → (¬ p 105) → False)
    (c394 : (¬ p 157) → (p 156) → False)
    (c395 : (¬ p 157) → (p 106) → False)
    (c396 : (p 157) → (¬ p 156) → (¬ p 106) → False)
    (c397 : (¬ p 158) → (p 157) → False)
    (c398 : (¬ p 158) → (p 107) → False)
    (c399 : (p 158) → (¬ p 157) → (¬ p 107) → False)
    (c400 : (¬ p 159) → (p 158) → False)
    (c401 : (¬ p 159) → (p 108) → False)
    (c402 : (p 159) → (¬ p 158) → (¬ p 108) → False)
    (c403 : (¬ p 160) → (p 159) → False)
    (c404 : (¬ p 160) → (p 109) → False)
    (c405 : (p 160) → (¬ p 159) → (¬ p 109) → False)
    (c406 : (¬ p 161) → (p 160) → False)
    (c407 : (¬ p 161) → (p 110) → False)
    (c408 : (p 161) → (¬ p 160) → (¬ p 110) → False)
    (c409 : (¬ p 162) → (p 161) → False)
    (c410 : (¬ p 162) → (p 111) → False)
    (c411 : (p 162) → (¬ p 161) → (¬ p 111) → False)
    (c412 : (¬ p 163) → (p 162) → False)
    (c413 : (¬ p 163) → (p 112) → False)
    (c414 : (p 163) → (¬ p 162) → (¬ p 112) → False)
    (c415 : (¬ p 164) → (p 163) → False)
    (c416 : (¬ p 164) → (p 113) → False)
    (c417 : (p 164) → (¬ p 163) → (¬ p 113) → False)
    (c418 : (¬ p 165) → (p 164) → False)
    (c419 : (¬ p 165) → (p 114) → False)
    (c420 : (p 165) → (¬ p 164) → (¬ p 114) → False)
    (c421 : (¬ p 166) → (p 165) → False)
    (c422 : (¬ p 166) → (p 115) → False)
    (c423 : (p 166) → (¬ p 165) → (¬ p 115) → False)
    (c424 : (¬ p 167) → (p 166) → False)
    (c425 : (¬ p 167) → (p 116) → False)
    (c426 : (p 167) → (¬ p 166) → (¬ p 116) → False)
    (c427 : (¬ p 168) → (p 167) → False)
    (c428 : (¬ p 168) → (p 117) → False)
    (c429 : (p 168) → (¬ p 167) → (¬ p 117) → False)
    (c430 : (¬ p 169) → (p 168) → False)
    (c431 : (¬ p 169) → (p 118) → False)
    (c432 : (p 169) → (¬ p 168) → (¬ p 118) → False)
    (c433 : (¬ p 170) → (p 169) → False)
    (c434 : (¬ p 170) → (p 119) → False)
    (c435 : (p 170) → (¬ p 169) → (¬ p 119) → False)
    (c436 : (¬ p 171) → (p 170) → False)
    (c437 : (¬ p 171) → (p 120) → False)
    (c438 : (p 171) → (¬ p 170) → (¬ p 120) → False)
    (c439 : (¬ p 172) → (p 171) → False)
    (c440 : (¬ p 172) → (p 121) → False)
    (c441 : (p 172) → (¬ p 171) → (¬ p 121) → False)
    (c442 : (¬ p 173) → (p 172) → False)
    (c443 : (¬ p 173) → (p 122) → False)
    (c444 : (p 173) → (¬ p 172) → (¬ p 122) → False)
    (c445 : (¬ p 174) → (p 173) → False)
    (c446 : (¬ p 174) → (p 123) → False)
    (c447 : (p 174) → (¬ p 173) → (¬ p 123) → False)
    (c448 : (¬ p 175) → (p 174) → False)
    (c449 : (¬ p 175) → (p 124) → False)
    (c450 : (p 175) → (¬ p 174) → (¬ p 124) → False)
    (c451 : (¬ p 176) → (p 175) → False)
    (c452 : (¬ p 176) → (p 125) → False)
    (c453 : (p 176) → (¬ p 175) → (¬ p 125) → False)
    (c454 : (¬ p 177) → (p 176) → False)
    (c455 : (¬ p 177) → (p 126) → False)
    (c456 : (p 177) → (¬ p 176) → (¬ p 126) → False)
    (c457 : (¬ p 178) → (p 177) → False)
    (c458 : (¬ p 178) → (p 127) → False)
    (c459 : (p 178) → (¬ p 177) → (¬ p 127) → False)
    (c460 : (¬ p 179) → (p 178) → False)
    (c461 : (¬ p 179) → (p 128) → False)
    (c462 : (p 179) → (¬ p 178) → (¬ p 128) → False)
    (c463 : (¬ p 180) → (p 179) → False)
    (c464 : (¬ p 180) → (p 129) → False)
    (c465 : (p 180) → (¬ p 179) → (¬ p 129) → False)
    (c466 : (¬ p 181) → (p 180) → False)
    (c467 : (¬ p 181) → (p 130) → False)
    (c468 : (p 181) → (¬ p 180) → (¬ p 130) → False)
    (c469 : (¬ p 182) → (p 181) → False)
    (c470 : (¬ p 182) → (p 131) → False)
    (c471 : (p 182) → (¬ p 181) → (¬ p 131) → False)
    (c472 : (¬ p 183) → (p 182) → False)
    (c473 : (¬ p 183) → (p 132) → False)
    (c474 : (p 183) → (¬ p 182) → (¬ p 132) → False)
    (c475 : (¬ p 184) → (p 183) → False)
    (c476 : (¬ p 184) → (p 133) → False)
    (c477 : (p 184) → (¬ p 183) → (¬ p 133) → False)
    (c478 : (¬ p 185) → (p 184) → False)
    (c479 : (¬ p 185) → (p 134) → False)
    (c480 : (p 185) → (¬ p 184) → (¬ p 134) → False)
    (c481 : (¬ p 186) → (p 185) → False)
    (c482 : (¬ p 186) → (p 135) → False)
    (c483 : (p 186) → (¬ p 185) → (¬ p 135) → False)
    (c484 : (¬ p 187) → (p 186) → False)
    (c485 : (¬ p 187) → (p 136) → False)
    (c486 : (p 187) → (¬ p 186) → (¬ p 136) → False)
    (c487 : (¬ p 188) → (p 187) → False)
    (c488 : (¬ p 188) → (p 137) → False)
    (c489 : (p 188) → (¬ p 187) → (¬ p 137) → False)
    (c490 : (¬ p 189) → (p 188) → False)
    (c491 : (¬ p 189) → (p 138) → False)
    (c492 : (p 189) → (¬ p 188) → (¬ p 138) → False)
    (c493 : (¬ p 190) → (p 189) → False)
    (c494 : (¬ p 190) → (p 139) → False)
    (c495 : (p 190) → (¬ p 189) → (¬ p 139) → False)
    (c496 : (¬ p 191) → (p 190) → False)
    (c497 : (¬ p 191) → (p 140) → False)
    (c498 : (p 191) → (¬ p 190) → (¬ p 140) → False)
    (c499 : (¬ p 192) → (p 191) → False)
    (c500 : (¬ p 192) → (p 141) → False)
    (c501 : (p 192) → (¬ p 191) → (¬ p 141) → False)
    (c502 : (¬ p 193) → (p 192) → False)
    (c503 : (¬ p 193) → (p 142) → False)
    (c504 : (p 193) → (¬ p 192) → (¬ p 142) → False)
    (c505 : (¬ p 90) → (¬ p 193) → False)
    (c506 : (p 90) → (p 193) → False)
    : False := by
  classical
  have c507 : (p 84) → (¬ p 90) → False := by
    intro a0 a1
    have u0 : p 85 := Classical.byContradiction (fun h => c178 h a0)
    have u1 : p 89 := Classical.byContradiction (fun h => c190 h a0)
    have u2 : p 86 := Classical.byContradiction (fun h => c181 h u0)
    have u3 : ¬ p 88 := fun h => c195 a1 h u1
    have u4 : p 87 := Classical.byContradiction (fun h => c184 h u2)
    exact c187 u3 u4
  have c508 : (p 142) → (¬ p 73) → False := by
    intro a0 a1
    have u0 : p 12 := Classical.byContradiction (fun h => c349 a0 h)
    have u1 : p 25 := Classical.byContradiction (fun h => c350 a0 h)
    have u2 : p 70 := Classical.byContradiction (fun h => c133 h u0)
    have u3 : ¬ p 72 := fun h => c144 a1 u1 h
    have u4 : p 71 := Classical.byContradiction (fun h => c136 h u2)
    exact c139 u3 u4
  have c509 : (¬ p 0) → (p 143) → False := by
    intro a0 a1
    have u0 : ¬ p 91 := fun h => c196 h a0
    have u1 : ¬ p 92 := fun h => c199 h a0
    exact c354 a1 u0 u1
  have c510 : (p 143) → (¬ p 76) → False := by
    intro a0 a1
    have u0 : ¬ p 75 := fun h => c151 a1 h
    have u1 : ¬ p 74 := fun h => c148 u0 h
    have u2 : ¬ p 29 := fun h => c145 u1 h
    have u3 : ¬ p 41 := fun h => c152 a1 h
    have u4 : p 0 := Classical.byContradiction (fun h => c509 h a0)
    have u5 : p 26 := Classical.byContradiction (fun h => c1 h u4)
    have u6 : p 40 := Classical.byContradiction (fun h => c44 h u4)
    have u7 : p 27 := Classical.byContradiction (fun h => c4 h u5)
    have u8 : ¬ p 17 := fun h => c48 u3 h u6
    have u9 : p 28 := Classical.byContradiction (fun h => c7 h u7)
    have u10 : ¬ p 92 := fun h => c200 h u8
    have u11 : ¬ p 13 := fun h => c12 u2 h u9
    have u12 : p 91 := Classical.byContradiction (fun h => c354 a0 h u10)
    exact c197 u12 u11
  have c511 : (p 93) → (¬ p 65) → False := by
    intro a0 a1
    have u0 : p 0 := Classical.byContradiction (fun h => c202 a0 h)
    have u1 : p 23 := Classical.byContradiction (fun h => c203 a0 h)
    have u2 : p 63 := Classical.byContradiction (fun h => c113 h u0)
    have u3 : ¬ p 64 := fun h => c120 a1 u1 h
    exact c115 u3 u2
  have c512 : (p 94) → (¬ p 73) → False := by
    intro a0 a1
    have u0 : p 0 := Classical.byContradiction (fun h => c205 a0 h)
    have u1 : p 25 := Classical.byContradiction (fun h => c206 a0 h)
    have u2 : p 70 := Classical.byContradiction (fun h => c134 h u0)
    have u3 : ¬ p 72 := fun h => c144 a1 u1 h
    have u4 : p 71 := Classical.byContradiction (fun h => c136 h u2)
    exact c139 u3 u4
  have c513 : (p 95) → (¬ p 29) → False := by
    intro a0 a1
    have u0 : p 1 := Classical.byContradiction (fun h => c208 a0 h)
    have u1 : p 13 := Classical.byContradiction (fun h => c209 a0 h)
    have u2 : p 26 := Classical.byContradiction (fun h => c2 h u0)
    have u3 : ¬ p 28 := fun h => c12 a1 u1 h
    have u4 : p 27 := Classical.byContradiction (fun h => c4 h u2)
    exact c7 u3 u4
  have c514 : (p 96) → (¬ p 90) → False := by
    intro a0 a1
    have u0 : p 1 := Classical.byContradiction (fun h => c211 a0 h)
    have u1 : p 14 := Classical.byContradiction (fun h => c212 a0 h)
    have u2 : p 85 := Classical.byContradiction (fun h => c179 h u0)
    have u3 : p 89 := Classical.byContradiction (fun h => c191 h u1)
    have u4 : p 86 := Classical.byContradiction (fun h => c181 h u2)
    have u5 : ¬ p 88 := fun h => c195 a1 h u3
    have u6 : p 87 := Classical.byContradiction (fun h => c184 h u4)
    exact c187 u5 u6
  have c515 : (p 97) → (¬ p 45) → False := by
    intro a0 a1
    have u0 : p 1 := Classical.byContradiction (fun h => c214 a0 h)
    have u1 : p 18 := Classical.byContradiction (fun h => c215 a0 h)
    have u2 : p 44 := Classical.byContradiction (fun h => c56 h u0)
    exact c60 a1 u1 u2
  have c516 : (p 98) → (¬ p 69) → False := by
    intro a0 a1
    have u0 : p 1 := Classical.byContradiction (fun h => c217 a0 h)
    have u1 : p 24 := Classical.byContradiction (fun h => c218 a0 h)
    have u2 : p 67 := Classical.byContradiction (fun h => c125 h u0)
    have u3 : ¬ p 68 := fun h => c132 a1 u1 h
    exact c127 u3 u2
  have c517 : (p 99) → (¬ p 90) → False := by
    intro a0 a1
    have u0 : p 2 := Classical.byContradiction (fun h => c220 a0 h)
    have u1 : p 14 := Classical.byContradiction (fun h => c221 a0 h)
    have u2 : p 86 := Classical.byContradiction (fun h => c182 h u0)
    have u3 : p 89 := Classical.byContradiction (fun h => c191 h u1)
    have u4 : p 87 := Classical.byContradiction (fun h => c184 h u2)
    have u5 : ¬ p 88 := fun h => c195 a1 h u3
    exact c187 u5 u4
  have c518 : (p 100) → (¬ p 33) → False := by
    intro a0 a1
    have u0 : p 2 := Classical.byContradiction (fun h => c223 a0 h)
    have u1 : p 15 := Classical.byContradiction (fun h => c224 a0 h)
    have u2 : p 30 := Classical.byContradiction (fun h => c13 h u0)
    have u3 : ¬ p 32 := fun h => c24 a1 u1 h
    have u4 : p 31 := Classical.byContradiction (fun h => c16 h u2)
    exact c19 u3 u4
  have c519 : (p 101) → (¬ p 49) → False := by
    intro a0 a1
    have u0 : p 2 := Classical.byContradiction (fun h => c226 a0 h)
    have u1 : p 19 := Classical.byContradiction (fun h => c227 a0 h)
    have u2 : p 48 := Classical.byContradiction (fun h => c68 h u0)
    exact c72 a1 u1 u2
  have c520 : (p 102) → (¬ p 73) → False := by
    intro a0 a1
    have u0 : p 2 := Classical.byContradiction (fun h => c229 a0 h)
    have u1 : p 25 := Classical.byContradiction (fun h => c230 a0 h)
    have u2 : p 71 := Classical.byContradiction (fun h => c137 h u0)
    have u3 : ¬ p 72 := fun h => c144 a1 u1 h
    exact c139 u3 u2
  have c521 : (p 103) → (¬ p 29) → False := by
    intro a0 a1
    have u0 : p 3 := Classical.byContradiction (fun h => c232 a0 h)
    have u1 : p 13 := Classical.byContradiction (fun h => c233 a0 h)
    have u2 : p 27 := Classical.byContradiction (fun h => c5 h u0)
    have u3 : ¬ p 28 := fun h => c12 a1 u1 h
    exact c7 u3 u2
  have c522 : (p 104) → (¬ p 33) → False := by
    intro a0 a1
    have u0 : p 3 := Classical.byContradiction (fun h => c235 a0 h)
    have u1 : p 15 := Classical.byContradiction (fun h => c236 a0 h)
    have u2 : p 30 := Classical.byContradiction (fun h => c14 h u0)
    have u3 : ¬ p 32 := fun h => c24 a1 u1 h
    have u4 : p 31 := Classical.byContradiction (fun h => c16 h u2)
    exact c19 u3 u4
  have c523 : (p 105) → (¬ p 37) → False := by
    intro a0 a1
    have u0 : p 3 := Classical.byContradiction (fun h => c238 a0 h)
    have u1 : p 16 := Classical.byContradiction (fun h => c239 a0 h)
    have u2 : p 34 := Classical.byContradiction (fun h => c25 h u0)
    have u3 : ¬ p 36 := fun h => c36 a1 u1 h
    have u4 : p 35 := Classical.byContradiction (fun h => c28 h u2)
    exact c31 u3 u4
  have c524 : (p 106) → (¬ p 53) → False := by
    intro a0 a1
    have u0 : p 3 := Classical.byContradiction (fun h => c241 a0 h)
    have u1 : p 20 := Classical.byContradiction (fun h => c242 a0 h)
    have u2 : p 52 := Classical.byContradiction (fun h => c80 h u0)
    exact c84 a1 u1 u2
  have c525 : (p 107) → (¬ p 90) → False := by
    intro a0 a1
    have u0 : p 4 := Classical.byContradiction (fun h => c244 a0 h)
    have u1 : p 14 := Classical.byContradiction (fun h => c245 a0 h)
    have u2 : p 87 := Classical.byContradiction (fun h => c185 h u0)
    have u3 : p 89 := Classical.byContradiction (fun h => c191 h u1)
    have u4 : p 88 := Classical.byContradiction (fun h => c187 h u2)
    exact c195 a1 u4 u3
  have c526 : (p 108) → (¬ p 37) → False := by
    intro a0 a1
    have u0 : p 4 := Classical.byContradiction (fun h => c247 a0 h)
    have u1 : p 16 := Classical.byContradiction (fun h => c248 a0 h)
    have u2 : p 34 := Classical.byContradiction (fun h => c26 h u0)
    have u3 : ¬ p 36 := fun h => c36 a1 u1 h
    have u4 : p 35 := Classical.byContradiction (fun h => c28 h u2)
    exact c31 u3 u4
  have c527 : (p 109) → (¬ p 41) → False := by
    intro a0 a1
    have u0 : p 4 := Classical.byContradiction (fun h => c250 a0 h)
    have u1 : p 17 := Classical.byContradiction (fun h => c251 a0 h)
    have u2 : p 38 := Classical.byContradiction (fun h => c37 h u0)
    have u3 : ¬ p 40 := fun h => c48 a1 u1 h
    have u4 : p 39 := Classical.byContradiction (fun h => c40 h u2)
    exact c43 u3 u4
  have c528 : (p 110) → (¬ p 57) → False := by
    intro a0 a1
    have u0 : p 4 := Classical.byContradiction (fun h => c253 a0 h)
    have u1 : p 21 := Classical.byContradiction (fun h => c254 a0 h)
    have u2 : p 56 := Classical.byContradiction (fun h => c92 h u0)
    exact c96 a1 u1 u2
  have c529 : (p 111) → (¬ p 33) → False := by
    intro a0 a1
    have u0 : p 5 := Classical.byContradiction (fun h => c256 a0 h)
    have u1 : p 15 := Classical.byContradiction (fun h => c257 a0 h)
    have u2 : p 31 := Classical.byContradiction (fun h => c17 h u0)
    have u3 : ¬ p 32 := fun h => c24 a1 u1 h
    exact c19 u3 u2
  have c530 : (p 112) → (¬ p 41) → False := by
    intro a0 a1
    have u0 : p 5 := Classical.byContradiction (fun h => c259 a0 h)
    have u1 : p 17 := Classical.byContradiction (fun h => c260 a0 h)
    have u2 : p 38 := Classical.byContradiction (fun h => c38 h u0)
    have u3 : ¬ p 40 := fun h => c48 a1 u1 h
    have u4 : p 39 := Classical.byContradiction (fun h => c40 h u2)
    exact c43 u3 u4
  have c531 : (p 113) → (¬ p 45) → False := by
    intro a0 a1
    have u0 : p 5 := Classical.byContradiction (fun h => c262 a0 h)
    have u1 : p 18 := Classical.byContradiction (fun h => c263 a0 h)
    have u2 : p 42 := Classical.byContradiction (fun h => c49 h u0)
    have u3 : ¬ p 44 := fun h => c60 a1 u1 h
    have u4 : p 43 := Classical.byContradiction (fun h => c52 h u2)
    exact c55 u3 u4
  have c532 : (p 114) → (¬ p 61) → False := by
    intro a0 a1
    have u0 : p 5 := Classical.byContradiction (fun h => c265 a0 h)
    have u1 : p 22 := Classical.byContradiction (fun h => c266 a0 h)
    have u2 : p 60 := Classical.byContradiction (fun h => c104 h u0)
    exact c108 a1 u1 u2
  have c533 : (p 115) → (¬ p 37) → False := by
    intro a0 a1
    have u0 : p 6 := Classical.byContradiction (fun h => c268 a0 h)
    have u1 : p 16 := Classical.byContradiction (fun h => c269 a0 h)
    have u2 : p 35 := Classical.byContradiction (fun h => c29 h u0)
    have u3 : ¬ p 36 := fun h => c36 a1 u1 h
    exact c31 u3 u2
  have c534 : (p 116) → (¬ p 45) → False := by
    intro a0 a1
    have u0 : p 6 := Classical.byContradiction (fun h => c271 a0 h)
    have u1 : p 18 := Classical.byContradiction (fun h => c272 a0 h)
    have u2 : p 42 := Classical.byContradiction (fun h => c50 h u0)
    have u3 : ¬ p 44 := fun h => c60 a1 u1 h
    have u4 : p 43 := Classical.byContradiction (fun h => c52 h u2)
    exact c55 u3 u4
  have c535 : (p 117) → (¬ p 49) → False := by
    intro a0 a1
    have u0 : p 6 := Classical.byContradiction (fun h => c274 a0 h)
    have u1 : p 19 := Classical.byContradiction (fun h => c275 a0 h)
    have u2 : p 46 := Classical.byContradiction (fun h => c61 h u0)
    have u3 : ¬ p 48 := fun h => c72 a1 u1 h
    have u4 : p 47 := Classical.byContradiction (fun h => c64 h u2)
    exact c67 u3 u4
  have c536 : (p 118) → (¬ p 65) → False := by
    intro a0 a1
    have u0 : p 6 := Classical.byContradiction (fun h => c277 a0 h)
    have u1 : p 23 := Classical.byContradiction (fun h => c278 a0 h)
    have u2 : p 64 := Classical.byContradiction (fun h => c116 h u0)
    exact c120 a1 u1 u2
  have c537 : (p 119) → (¬ p 41) → False := by
    intro a0 a1
    have u0 : p 7 := Classical.byContradiction (fun h => c280 a0 h)
    have u1 : p 17 := Classical.byContradiction (fun h => c281 a0 h)
    have u2 : p 39 := Classical.byContradiction (fun h => c41 h u0)
    have u3 : ¬ p 40 := fun h => c48 a1 u1 h
    exact c43 u3 u2
  have c538 : (p 120) → (¬ p 49) → False := by
    intro a0 a1
    have u0 : p 7 := Classical.byContradiction (fun h => c283 a0 h)
    have u1 : p 19 := Classical.byContradiction (fun h => c284 a0 h)
    have u2 : p 46 := Classical.byContradiction (fun h => c62 h u0)
    have u3 : ¬ p 48 := fun h => c72 a1 u1 h
    have u4 : p 47 := Classical.byContradiction (fun h => c64 h u2)
    exact c67 u3 u4
  have c539 : (p 121) → (¬ p 53) → False := by
    intro a0 a1
    have u0 : p 7 := Classical.byContradiction (fun h => c286 a0 h)
    have u1 : p 20 := Classical.byContradiction (fun h => c287 a0 h)
    have u2 : p 50 := Classical.byContradiction (fun h => c73 h u0)
    have u3 : ¬ p 52 := fun h => c84 a1 u1 h
    have u4 : p 51 := Classical.byContradiction (fun h => c76 h u2)
    exact c79 u3 u4
  have c540 : (p 122) → (¬ p 69) → False := by
    intro a0 a1
    have u0 : p 7 := Classical.byContradiction (fun h => c289 a0 h)
    have u1 : p 24 := Classical.byContradiction (fun h => c290 a0 h)
    have u2 : p 68 := Classical.byContradiction (fun h => c128 h u0)
    exact c132 a1 u1 u2
  have c541 : (p 123) → (¬ p 45) → False := by
    intro a0 a1
    have u0 : p 8 := Classical.byContradiction (fun h => c292 a0 h)
    have u1 : p 18 := Classical.byContradiction (fun h => c293 a0 h)
    have u2 : p 43 := Classical.byContradiction (fun h => c53 h u0)
    have u3 : ¬ p 44 := fun h => c60 a1 u1 h
    exact c55 u3 u2
  have c542 : (p 124) → (¬ p 53) → False := by
    intro a0 a1
    have u0 : p 8 := Classical.byContradiction (fun h => c295 a0 h)
    have u1 : p 20 := Classical.byContradiction (fun h => c296 a0 h)
    have u2 : p 50 := Classical.byContradiction (fun h => c74 h u0)
    have u3 : ¬ p 52 := fun h => c84 a1 u1 h
    have u4 : p 51 := Classical.byContradiction (fun h => c76 h u2)
    exact c79 u3 u4
  have c543 : (p 125) → (¬ p 57) → False := by
    intro a0 a1
    have u0 : p 8 := Classical.byContradiction (fun h => c298 a0 h)
    have u1 : p 21 := Classical.byContradiction (fun h => c299 a0 h)
    have u2 : p 54 := Classical.byContradiction (fun h => c85 h u0)
    have u3 : ¬ p 56 := fun h => c96 a1 u1 h
    have u4 : p 55 := Classical.byContradiction (fun h => c88 h u2)
    exact c91 u3 u4
  have c544 : (p 126) → (¬ p 73) → False := by
    intro a0 a1
    have u0 : p 8 := Classical.byContradiction (fun h => c301 a0 h)
    have u1 : p 25 := Classical.byContradiction (fun h => c302 a0 h)
    have u2 : p 72 := Classical.byContradiction (fun h => c140 h u0)
    exact c144 a1 u1 u2
  have c545 : (p 127) → (¬ p 29) → False := by
    intro a0 a1
    have u0 : p 9 := Classical.byContradiction (fun h => c304 a0 h)
    have u1 : p 13 := Classical.byContradiction (fun h => c305 a0 h)
    have u2 : p 28 := Classical.byContradiction (fun h => c8 h u0)
    exact c12 a1 u1 u2
  have c546 : (p 128) → (¬ p 49) → False := by
    intro a0 a1
    have u0 : p 9 := Classical.byContradiction (fun h => c307 a0 h)
    have u1 : p 19 := Classical.byContradiction (fun h => c308 a0 h)
    have u2 : p 47 := Classical.byContradiction (fun h => c65 h u0)
    have u3 : ¬ p 48 := fun h => c72 a1 u1 h
    exact c67 u3 u2
  have c547 : (p 129) → (¬ p 57) → False := by
    intro a0 a1
    have u0 : p 9 := Classical.byContradiction (fun h => c310 a0 h)
    have u1 : p 21 := Classical.byContradiction (fun h => c311 a0 h)
    have u2 : p 54 := Classical.byContradiction (fun h => c86 h u0)
    have u3 : ¬ p 56 := fun h => c96 a1 u1 h
    have u4 : p 55 := Classical.byContradiction (fun h => c88 h u2)
    exact c91 u3 u4
  have c548 : (p 130) → (¬ p 61) → False := by
    intro a0 a1
    have u0 : p 9 := Classical.byContradiction (fun h => c313 a0 h)
    have u1 : p 22 := Classical.byContradiction (fun h => c314 a0 h)
    have u2 : p 58 := Classical.byContradiction (fun h => c97 h u0)
    have u3 : ¬ p 60 := fun h => c108 a1 u1 h
    have u4 : p 59 := Classical.byContradiction (fun h => c100 h u2)
    exact c103 u3 u4
  have c549 : (p 131) → (¬ p 90) → False := by
    intro a0 a1
    have u0 : p 10 := Classical.byContradiction (fun h => c316 a0 h)
    have u1 : p 14 := Classical.byContradiction (fun h => c317 a0 h)
    have u2 : p 88 := Classical.byContradiction (fun h => c188 h u0)
    have u3 : p 89 := Classical.byContradiction (fun h => c191 h u1)
    exact c195 a1 u2 u3
  have c550 : (p 132) → (¬ p 53) → False := by
    intro a0 a1
    have u0 : p 10 := Classical.byContradiction (fun h => c319 a0 h)
    have u1 : p 20 := Classical.byContradiction (fun h => c320 a0 h)
    have u2 : p 51 := Classical.byContradiction (fun h => c77 h u0)
    have u3 : ¬ p 52 := fun h => c84 a1 u1 h
    exact c79 u3 u2
  have c551 : (p 133) → (¬ p 61) → False := by
    intro a0 a1
    have u0 : p 10 := Classical.byContradiction (fun h => c322 a0 h)
    have u1 : p 22 := Classical.byContradiction (fun h => c323 a0 h)
    have u2 : p 58 := Classical.byContradiction (fun h => c98 h u0)
    have u3 : ¬ p 60 := fun h => c108 a1 u1 h
    have u4 : p 59 := Classical.byContradiction (fun h => c100 h u2)
    exact c103 u3 u4
  have c552 : (p 134) → (¬ p 65) → False := by
    intro a0 a1
    have u0 : p 10 := Classical.byContradiction (fun h => c325 a0 h)
    have u1 : p 23 := Classical.byContradiction (fun h => c326 a0 h)
    have u2 : p 62 := Classical.byContradiction (fun h => c109 h u0)
    have u3 : ¬ p 64 := fun h => c120 a1 u1 h
    have u4 : p 63 := Classical.byContradiction (fun h => c112 h u2)
    exact c115 u3 u4
  have c553 : (p 135) → (¬ p 33) → False := by
    intro a0 a1
    have u0 : p 11 := Classical.byContradiction (fun h => c328 a0 h)
    have u1 : p 15 := Classical.byContradiction (fun h => c329 a0 h)
    have u2 : p 32 := Classical.byContradiction (fun h => c20 h u0)
    exact c24 a1 u1 u2
  have c554 : (p 136) → (¬ p 57) → False := by
    intro a0 a1
    have u0 : p 11 := Classical.byContradiction (fun h => c331 a0 h)
    have u1 : p 21 := Classical.byContradiction (fun h => c332 a0 h)
    have u2 : p 55 := Classical.byContradiction (fun h => c89 h u0)
    have u3 : ¬ p 56 := fun h => c96 a1 u1 h
    exact c91 u3 u2
  have c555 : (p 137) → (¬ p 65) → False := by
    intro a0 a1
    have u0 : p 11 := Classical.byContradiction (fun h => c334 a0 h)
    have u1 : p 23 := Classical.byContradiction (fun h => c335 a0 h)
    have u2 : p 62 := Classical.byContradiction (fun h => c110 h u0)
    have u3 : ¬ p 64 := fun h => c120 a1 u1 h
    have u4 : p 63 := Classical.byContradiction (fun h => c112 h u2)
    exact c115 u3 u4
  have c556 : (p 138) → (¬ p 69) → False := by
    intro a0 a1
    have u0 : p 11 := Classical.byContradiction (fun h => c337 a0 h)
    have u1 : p 24 := Classical.byContradiction (fun h => c338 a0 h)
    have u2 : p 66 := Classical.byContradiction (fun h => c121 h u0)
    have u3 : ¬ p 68 := fun h => c132 a1 u1 h
    have u4 : p 67 := Classical.byContradiction (fun h => c124 h u2)
    exact c127 u3 u4
  have c557 : (p 139) → (¬ p 37) → False := by
    intro a0 a1
    have u0 : p 12 := Classical.byContradiction (fun h => c340 a0 h)
    have u1 : p 16 := Classical.byContradiction (fun h => c341 a0 h)
    have u2 : p 36 := Classical.byContradiction (fun h => c32 h u0)
    exact c36 a1 u1 u2
  have c558 : (p 140) → (¬ p 61) → False := by
    intro a0 a1
    have u0 : p 12 := Classical.byContradiction (fun h => c343 a0 h)
    have u1 : p 22 := Classical.byContradiction (fun h => c344 a0 h)
    have u2 : p 59 := Classical.byContradiction (fun h => c101 h u0)
    have u3 : ¬ p 60 := fun h => c108 a1 u1 h
    exact c103 u3 u2
  have c559 : (p 141) → (¬ p 69) → False := by
    intro a0 a1
    have u0 : p 12 := Classical.byContradiction (fun h => c346 a0 h)
    have u1 : p 24 := Classical.byContradiction (fun h => c347 a0 h)
    have u2 : p 66 := Classical.byContradiction (fun h => c122 h u0)
    have u3 : ¬ p 68 := fun h => c132 a1 u1 h
    have u4 : p 67 := Classical.byContradiction (fun h => c124 h u2)
    exact c127 u3 u4
  have c560 : (p 193) → False := by
    intro a0
    have u0 : ¬ p 90 := fun h => c506 h a0
    have u1 : ¬ p 84 := fun h => c507 h u0
    have u2 : ¬ p 83 := fun h => c175 u1 h
    have u3 : ¬ p 73 := fun h => c176 u1 h
    have u4 : ¬ p 82 := fun h => c172 u2 h
    have u5 : ¬ p 69 := fun h => c173 u2 h
    have u6 : ¬ p 81 := fun h => c169 u4 h
    have u7 : ¬ p 65 := fun h => c170 u4 h
    have u8 : ¬ p 80 := fun h => c166 u6 h
    have u9 : ¬ p 61 := fun h => c167 u6 h
    have u10 : ¬ p 79 := fun h => c163 u8 h
    have u11 : ¬ p 57 := fun h => c164 u8 h
    have u12 : ¬ p 78 := fun h => c160 u10 h
    have u13 : ¬ p 53 := fun h => c161 u10 h
    have u14 : ¬ p 77 := fun h => c157 u12 h
    have u15 : ¬ p 49 := fun h => c158 u12 h
    have u16 : ¬ p 76 := fun h => c154 u14 h
    have u17 : ¬ p 45 := fun h => c155 u14 h
    have u18 : ¬ p 75 := fun h => c151 u16 h
    have u19 : ¬ p 41 := fun h => c152 u16 h
    have u20 : ¬ p 74 := fun h => c148 u18 h
    have u21 : ¬ p 37 := fun h => c149 u18 h
    have u22 : ¬ p 29 := fun h => c145 u20 h
    have u23 : ¬ p 33 := fun h => c146 u20 h
    have u24 : ¬ p 142 := fun h => c508 h u3
    have u25 : ¬ p 143 := fun h => c510 h u16
    have u26 : ¬ p 93 := fun h => c511 h u7
    have u27 : ¬ p 144 := fun h => c357 h u25 u26
    have u28 : ¬ p 94 := fun h => c512 h u3
    have u29 : ¬ p 145 := fun h => c360 h u27 u28
    have u30 : ¬ p 95 := fun h => c513 h u22
    have u31 : ¬ p 146 := fun h => c363 h u29 u30
    have u32 : ¬ p 96 := fun h => c514 h u0
    have u33 : ¬ p 147 := fun h => c366 h u31 u32
    have u34 : ¬ p 97 := fun h => c515 h u17
    have u35 : ¬ p 148 := fun h => c369 h u33 u34
    have u36 : ¬ p 98 := fun h => c516 h u5
    have u37 : ¬ p 149 := fun h => c372 h u35 u36
    have u38 : ¬ p 99 := fun h => c517 h u0
    have u39 : ¬ p 150 := fun h => c375 h u37 u38
    have u40 : ¬ p 100 := fun h => c518 h u23
    have u41 : ¬ p 151 := fun h => c378 h u39 u40
    have u42 : ¬ p 101 := fun h => c519 h u15
    have u43 : ¬ p 152 := fun h => c381 h u41 u42
    have u44 : ¬ p 102 := fun h => c520 h u3
    have u45 : ¬ p 153 := fun h => c384 h u43 u44
    have u46 : ¬ p 103 := fun h => c521 h u22
    have u47 : ¬ p 154 := fun h => c387 h u45 u46
    have u48 : ¬ p 104 := fun h => c522 h u23
    have u49 : ¬ p 155 := fun h => c390 h u47 u48
    have u50 : ¬ p 105 := fun h => c523 h u21
    have u51 : ¬ p 156 := fun h => c393 h u49 u50
    have u52 : ¬ p 106 := fun h => c524 h u13
    have u53 : ¬ p 157 := fun h => c396 h u51 u52
    have u54 : ¬ p 107 := fun h => c525 h u0
    have u55 : ¬ p 158 := fun h => c399 h u53 u54
    have u56 : ¬ p 108 := fun h => c526 h u21
    have u57 : ¬ p 159 := fun h => c402 h u55 u56
    have u58 : ¬ p 109 := fun h => c527 h u19
    have u59 : ¬ p 160 := fun h => c405 h u57 u58
    have u60 : ¬ p 110 := fun h => c528 h u11
    have u61 : ¬ p 161 := fun h => c408 h u59 u60
    have u62 : ¬ p 111 := fun h => c529 h u23
    have u63 : ¬ p 162 := fun h => c411 h u61 u62
    have u64 : ¬ p 112 := fun h => c530 h u19
    have u65 : ¬ p 163 := fun h => c414 h u63 u64
    have u66 : ¬ p 113 := fun h => c531 h u17
    have u67 : ¬ p 164 := fun h => c417 h u65 u66
    have u68 : ¬ p 114 := fun h => c532 h u9
    have u69 : ¬ p 165 := fun h => c420 h u67 u68
    have u70 : ¬ p 115 := fun h => c533 h u21
    have u71 : ¬ p 166 := fun h => c423 h u69 u70
    have u72 : ¬ p 116 := fun h => c534 h u17
    have u73 : ¬ p 167 := fun h => c426 h u71 u72
    have u74 : ¬ p 117 := fun h => c535 h u15
    have u75 : ¬ p 168 := fun h => c429 h u73 u74
    have u76 : ¬ p 118 := fun h => c536 h u7
    have u77 : ¬ p 169 := fun h => c432 h u75 u76
    have u78 : ¬ p 119 := fun h => c537 h u19
    have u79 : ¬ p 170 := fun h => c435 h u77 u78
    have u80 : ¬ p 120 := fun h => c538 h u15
    have u81 : ¬ p 171 := fun h => c438 h u79 u80
    have u82 : ¬ p 121 := fun h => c539 h u13
    have u83 : ¬ p 172 := fun h => c441 h u81 u82
    have u84 : ¬ p 122 := fun h => c540 h u5
    have u85 : ¬ p 173 := fun h => c444 h u83 u84
    have u86 : ¬ p 123 := fun h => c541 h u17
    have u87 : ¬ p 174 := fun h => c447 h u85 u86
    have u88 : ¬ p 124 := fun h => c542 h u13
    have u89 : ¬ p 175 := fun h => c450 h u87 u88
    have u90 : ¬ p 125 := fun h => c543 h u11
    have u91 : ¬ p 176 := fun h => c453 h u89 u90
    have u92 : ¬ p 126 := fun h => c544 h u3
    have u93 : ¬ p 177 := fun h => c456 h u91 u92
    have u94 : ¬ p 127 := fun h => c545 h u22
    have u95 : ¬ p 178 := fun h => c459 h u93 u94
    have u96 : ¬ p 128 := fun h => c546 h u15
    have u97 : ¬ p 179 := fun h => c462 h u95 u96
    have u98 : ¬ p 129 := fun h => c547 h u11
    have u99 : ¬ p 180 := fun h => c465 h u97 u98
    have u100 : ¬ p 130 := fun h => c548 h u9
    have u101 : ¬ p 181 := fun h => c468 h u99 u100
    have u102 : ¬ p 131 := fun h => c549 h u0
    have u103 : ¬ p 182 := fun h => c471 h u101 u102
    have u104 : ¬ p 132 := fun h => c550 h u13
    have u105 : ¬ p 183 := fun h => c474 h u103 u104
    have u106 : ¬ p 133 := fun h => c551 h u9
    have u107 : ¬ p 184 := fun h => c477 h u105 u106
    have u108 : ¬ p 134 := fun h => c552 h u7
    have u109 : ¬ p 185 := fun h => c480 h u107 u108
    have u110 : ¬ p 135 := fun h => c553 h u23
    have u111 : ¬ p 186 := fun h => c483 h u109 u110
    have u112 : ¬ p 136 := fun h => c554 h u11
    have u113 : ¬ p 187 := fun h => c486 h u111 u112
    have u114 : ¬ p 137 := fun h => c555 h u7
    have u115 : ¬ p 188 := fun h => c489 h u113 u114
    have u116 : ¬ p 138 := fun h => c556 h u5
    have u117 : ¬ p 189 := fun h => c492 h u115 u116
    have u118 : ¬ p 139 := fun h => c557 h u21
    have u119 : ¬ p 190 := fun h => c495 h u117 u118
    have u120 : ¬ p 140 := fun h => c558 h u9
    have u121 : ¬ p 191 := fun h => c498 h u119 u120
    have u122 : ¬ p 141 := fun h => c559 h u5
    have u123 : p 192 := Classical.byContradiction (fun h => c504 a0 h u24)
    exact c501 u123 u121 u122
  have c561 : (p 192) → False := by
    intro a0
    have u0 : ¬ p 193 := fun h => c560 h
    exact c502 u0 a0
  have c562 : (p 142) → False := by
    intro a0
    have u0 : ¬ p 193 := fun h => c560 h
    exact c503 u0 a0
  have c563 : (¬ p 90) → False := by
    intro a0
    have u0 : ¬ p 193 := fun h => c560 h
    exact c505 a0 u0
  have c564 : (p 191) → False := by
    intro a0
    have u0 : ¬ p 192 := fun h => c561 h
    exact c499 u0 a0
  have c565 : (p 141) → False := by
    intro a0
    have u0 : ¬ p 192 := fun h => c561 h
    exact c500 u0 a0
  have c566 : (¬ p 88) → False := by
    intro a0
    have u0 : p 90 := Classical.byContradiction (fun h => c563 h)
    exact c193 u0 a0
  have c567 : (¬ p 89) → False := by
    intro a0
    have u0 : p 90 := Classical.byContradiction (fun h => c563 h)
    exact c194 u0 a0
  have c568 : (p 190) → False := by
    intro a0
    have u0 : ¬ p 191 := fun h => c564 h
    exact c496 u0 a0
  have c569 : (p 140) → False := by
    intro a0
    have u0 : ¬ p 191 := fun h => c564 h
    exact c497 u0 a0
  have c570 : (p 189) → False := by
    intro a0
    have u0 : ¬ p 190 := fun h => c568 h
    exact c493 u0 a0
  have c571 : (p 139) → False := by
    intro a0
    have u0 : ¬ p 190 := fun h => c568 h
    exact c494 u0 a0
  have c572 : (p 188) → False := by
    intro a0
    have u0 : ¬ p 189 := fun h => c570 h
    exact c490 u0 a0
  have c573 : (p 138) → False := by
    intro a0
    have u0 : ¬ p 189 := fun h => c570 h
    exact c491 u0 a0
  have c574 : (p 187) → False := by
    intro a0
    have u0 : ¬ p 188 := fun h => c572 h
    exact c487 u0 a0
  have c575 : (p 137) → False := by
    intro a0
    have u0 : ¬ p 188 := fun h => c572 h
    exact c488 u0 a0
  have c576 : (p 186) → False := by
    intro a0
    have u0 : ¬ p 187 := fun h => c574 h
    exact c484 u0 a0
  have c577 : (p 136) → False := by
    intro a0
    have u0 : ¬ p 187 := fun h => c574 h
    exact c485 u0 a0
  have c578 : (p 185) → False := by
    intro a0
    have u0 : ¬ p 186 := fun h => c576 h
    exact c481 u0 a0
  have c579 : (p 135) → False := by
    intro a0
    have u0 : ¬ p 186 := fun h => c576 h
    exact c482 u0 a0
  have c580 : (p 184) → False := by
    intro a0
    have u0 : ¬ p 185 := fun h => c578 h
    exact c478 u0 a0
  have c581 : (p 134) → False := by
    intro a0
    have u0 : ¬ p 185 := fun h => c578 h
    exact c479 u0 a0
  have c582 : (p 183) → False := by
    intro a0
    have u0 : ¬ p 184 := fun h => c580 h
    exact c475 u0 a0
  have c583 : (p 133) → False := by
    intro a0
    have u0 : ¬ p 184 := fun h => c580 h
    exact c476 u0 a0
  have c584 : (p 182) → False := by
    intro a0
    have u0 : ¬ p 183 := fun h => c582 h
    exact c472 u0 a0
  have c585 : (p 132) → False := by
    intro a0
    have u0 : ¬ p 183 := fun h => c582 h
    exact c473 u0 a0
  have c586 : (p 181) → False := by
    intro a0
    have u0 : ¬ p 182 := fun h => c584 h
    exact c469 u0 a0
  have c587 : (p 131) → False := by
    intro a0
    have u0 : ¬ p 182 := fun h => c584 h
    exact c470 u0 a0
  have c588 : (p 180) → False := by
    intro a0
    have u0 : ¬ p 181 := fun h => c586 h
    exact c466 u0 a0
  have c589 : (p 130) → False := by
    intro a0
    have u0 : ¬ p 181 := fun h => c586 h
    exact c467 u0 a0
  have c590 : (p 179) → False := by
    intro a0
    have u0 : ¬ p 180 := fun h => c588 h
    exact c463 u0 a0
  have c591 : (p 129) → False := by
    intro a0
    have u0 : ¬ p 180 := fun h => c588 h
    exact c464 u0 a0
  have c592 : (p 178) → False := by
    intro a0
    have u0 : ¬ p 179 := fun h => c590 h
    exact c460 u0 a0
  have c593 : (p 128) → False := by
    intro a0
    have u0 : ¬ p 179 := fun h => c590 h
    exact c461 u0 a0
  have c594 : (p 177) → False := by
    intro a0
    have u0 : ¬ p 178 := fun h => c592 h
    exact c457 u0 a0
  have c595 : (p 127) → False := by
    intro a0
    have u0 : ¬ p 178 := fun h => c592 h
    exact c458 u0 a0
  have c596 : (p 176) → False := by
    intro a0
    have u0 : ¬ p 177 := fun h => c594 h
    exact c454 u0 a0
  have c597 : (p 126) → False := by
    intro a0
    have u0 : ¬ p 177 := fun h => c594 h
    exact c455 u0 a0
  have c598 : (p 175) → False := by
    intro a0
    have u0 : ¬ p 176 := fun h => c596 h
    exact c451 u0 a0
  have c599 : (p 125) → False := by
    intro a0
    have u0 : ¬ p 176 := fun h => c596 h
    exact c452 u0 a0
  have c600 : (p 174) → False := by
    intro a0
    have u0 : ¬ p 175 := fun h => c598 h
    exact c448 u0 a0
  have c601 : (p 124) → False := by
    intro a0
    have u0 : ¬ p 175 := fun h => c598 h
    exact c449 u0 a0
  have c602 : (p 173) → False := by
    intro a0
    have u0 : ¬ p 174 := fun h => c600 h
    exact c445 u0 a0
  have c603 : (p 123) → False := by
    intro a0
    have u0 : ¬ p 174 := fun h => c600 h
    exact c446 u0 a0
  have c604 : (p 172) → False := by
    intro a0
    have u0 : ¬ p 173 := fun h => c602 h
    exact c442 u0 a0
  have c605 : (p 122) → False := by
    intro a0
    have u0 : ¬ p 173 := fun h => c602 h
    exact c443 u0 a0
  have c606 : (p 171) → False := by
    intro a0
    have u0 : ¬ p 172 := fun h => c604 h
    exact c439 u0 a0
  have c607 : (p 121) → False := by
    intro a0
    have u0 : ¬ p 172 := fun h => c604 h
    exact c440 u0 a0
  have c608 : (p 170) → False := by
    intro a0
    have u0 : ¬ p 171 := fun h => c606 h
    exact c436 u0 a0
  have c609 : (p 120) → False := by
    intro a0
    have u0 : ¬ p 171 := fun h => c606 h
    exact c437 u0 a0
  have c610 : (p 169) → False := by
    intro a0
    have u0 : ¬ p 170 := fun h => c608 h
    exact c433 u0 a0
  have c611 : (p 119) → False := by
    intro a0
    have u0 : ¬ p 170 := fun h => c608 h
    exact c434 u0 a0
  have c612 : (p 168) → False := by
    intro a0
    have u0 : ¬ p 169 := fun h => c610 h
    exact c430 u0 a0
  have c613 : (p 118) → False := by
    intro a0
    have u0 : ¬ p 169 := fun h => c610 h
    exact c431 u0 a0
  have c614 : (p 167) → False := by
    intro a0
    have u0 : ¬ p 168 := fun h => c612 h
    exact c427 u0 a0
  have c615 : (p 117) → False := by
    intro a0
    have u0 : ¬ p 168 := fun h => c612 h
    exact c428 u0 a0
  have c616 : (p 166) → False := by
    intro a0
    have u0 : ¬ p 167 := fun h => c614 h
    exact c424 u0 a0
  have c617 : (p 116) → False := by
    intro a0
    have u0 : ¬ p 167 := fun h => c614 h
    exact c425 u0 a0
  have c618 : (p 165) → False := by
    intro a0
    have u0 : ¬ p 166 := fun h => c616 h
    exact c421 u0 a0
  have c619 : (p 115) → False := by
    intro a0
    have u0 : ¬ p 166 := fun h => c616 h
    exact c422 u0 a0
  have c620 : (p 164) → False := by
    intro a0
    have u0 : ¬ p 165 := fun h => c618 h
    exact c418 u0 a0
  have c621 : (p 114) → False := by
    intro a0
    have u0 : ¬ p 165 := fun h => c618 h
    exact c419 u0 a0
  have c622 : (p 163) → False := by
    intro a0
    have u0 : ¬ p 164 := fun h => c620 h
    exact c415 u0 a0
  have c623 : (p 113) → False := by
    intro a0
    have u0 : ¬ p 164 := fun h => c620 h
    exact c416 u0 a0
  have c624 : (p 162) → False := by
    intro a0
    have u0 : ¬ p 163 := fun h => c622 h
    exact c412 u0 a0
  have c625 : (p 112) → False := by
    intro a0
    have u0 : ¬ p 163 := fun h => c622 h
    exact c413 u0 a0
  have c626 : (p 161) → False := by
    intro a0
    have u0 : ¬ p 162 := fun h => c624 h
    exact c409 u0 a0
  have c627 : (p 111) → False := by
    intro a0
    have u0 : ¬ p 162 := fun h => c624 h
    exact c410 u0 a0
  have c628 : (p 160) → False := by
    intro a0
    have u0 : ¬ p 161 := fun h => c626 h
    exact c406 u0 a0
  have c629 : (p 110) → False := by
    intro a0
    have u0 : ¬ p 161 := fun h => c626 h
    exact c407 u0 a0
  have c630 : (p 159) → False := by
    intro a0
    have u0 : ¬ p 160 := fun h => c628 h
    exact c403 u0 a0
  have c631 : (p 109) → False := by
    intro a0
    have u0 : ¬ p 160 := fun h => c628 h
    exact c404 u0 a0
  have c632 : (p 158) → False := by
    intro a0
    have u0 : ¬ p 159 := fun h => c630 h
    exact c400 u0 a0
  have c633 : (p 108) → False := by
    intro a0
    have u0 : ¬ p 159 := fun h => c630 h
    exact c401 u0 a0
  have c634 : (p 157) → False := by
    intro a0
    have u0 : ¬ p 158 := fun h => c632 h
    exact c397 u0 a0
  have c635 : (p 107) → False := by
    intro a0
    have u0 : ¬ p 158 := fun h => c632 h
    exact c398 u0 a0
  have c636 : (p 156) → False := by
    intro a0
    have u0 : ¬ p 157 := fun h => c634 h
    exact c394 u0 a0
  have c637 : (p 106) → False := by
    intro a0
    have u0 : ¬ p 157 := fun h => c634 h
    exact c395 u0 a0
  have c638 : (p 155) → False := by
    intro a0
    have u0 : ¬ p 156 := fun h => c636 h
    exact c391 u0 a0
  have c639 : (p 105) → False := by
    intro a0
    have u0 : ¬ p 156 := fun h => c636 h
    exact c392 u0 a0
  have c640 : (p 154) → False := by
    intro a0
    have u0 : ¬ p 155 := fun h => c638 h
    exact c388 u0 a0
  have c641 : (p 104) → False := by
    intro a0
    have u0 : ¬ p 155 := fun h => c638 h
    exact c389 u0 a0
  have c642 : (p 153) → False := by
    intro a0
    have u0 : ¬ p 154 := fun h => c640 h
    exact c385 u0 a0
  have c643 : (p 103) → False := by
    intro a0
    have u0 : ¬ p 154 := fun h => c640 h
    exact c386 u0 a0
  have c644 : (p 152) → False := by
    intro a0
    have u0 : ¬ p 153 := fun h => c642 h
    exact c382 u0 a0
  have c645 : (p 102) → False := by
    intro a0
    have u0 : ¬ p 153 := fun h => c642 h
    exact c383 u0 a0
  have c646 : (p 151) → False := by
    intro a0
    have u0 : ¬ p 152 := fun h => c644 h
    exact c379 u0 a0
  have c647 : (p 101) → False := by
    intro a0
    have u0 : ¬ p 152 := fun h => c644 h
    exact c380 u0 a0
  have c648 : (p 150) → False := by
    intro a0
    have u0 : ¬ p 151 := fun h => c646 h
    exact c376 u0 a0
  have c649 : (p 100) → False := by
    intro a0
    have u0 : ¬ p 151 := fun h => c646 h
    exact c377 u0 a0
  have c650 : (p 149) → False := by
    intro a0
    have u0 : ¬ p 150 := fun h => c648 h
    exact c373 u0 a0
  have c651 : (p 99) → False := by
    intro a0
    have u0 : ¬ p 150 := fun h => c648 h
    exact c374 u0 a0
  have c652 : (p 148) → False := by
    intro a0
    have u0 : ¬ p 149 := fun h => c650 h
    exact c370 u0 a0
  have c653 : (p 98) → False := by
    intro a0
    have u0 : ¬ p 149 := fun h => c650 h
    exact c371 u0 a0
  have c654 : (p 147) → False := by
    intro a0
    have u0 : ¬ p 148 := fun h => c652 h
    exact c367 u0 a0
  have c655 : (p 97) → False := by
    intro a0
    have u0 : ¬ p 148 := fun h => c652 h
    exact c368 u0 a0
  have c656 : (p 146) → False := by
    intro a0
    have u0 : ¬ p 147 := fun h => c654 h
    exact c364 u0 a0
  have c657 : (p 96) → False := by
    intro a0
    have u0 : ¬ p 147 := fun h => c654 h
    exact c365 u0 a0
  have c658 : (p 145) → False := by
    intro a0
    have u0 : ¬ p 146 := fun h => c656 h
    exact c361 u0 a0
  have c659 : (p 95) → False := by
    intro a0
    have u0 : ¬ p 146 := fun h => c656 h
    exact c362 u0 a0
  have c660 : (p 144) → False := by
    intro a0
    have u0 : ¬ p 145 := fun h => c658 h
    exact c358 u0 a0
  have c661 : (p 94) → False := by
    intro a0
    have u0 : ¬ p 145 := fun h => c658 h
    exact c359 u0 a0
  have c662 : (p 143) → False := by
    intro a0
    have u0 : ¬ p 144 := fun h => c660 h
    exact c355 u0 a0
  have c663 : (p 93) → False := by
    intro a0
    have u0 : ¬ p 144 := fun h => c660 h
    exact c356 u0 a0
  have c664 : (p 91) → False := by
    intro a0
    have u0 : ¬ p 143 := fun h => c662 h
    exact c352 u0 a0
  have c665 : (p 92) → False := by
    intro a0
    have u0 : ¬ p 143 := fun h => c662 h
    exact c353 u0 a0
  have c666 : (¬ p 84) → False := by
    intro a0
    have u0 : p 89 := Classical.byContradiction (fun h => c567 h)
    have u1 : ¬ p 96 := fun h => c657 h
    have u2 : ¬ p 99 := fun h => c651 h
    have u3 : ¬ p 107 := fun h => c635 h
    have u4 : ¬ p 131 := fun h => c587 h
    have u5 : p 88 := Classical.byContradiction (fun h => c566 h)
    have u6 : p 14 := Classical.byContradiction (fun h => c192 u0 a0 h)
    have u7 : ¬ p 1 := fun h => c213 u1 h u6
    have u8 : ¬ p 2 := fun h => c222 u2 h u6
    have u9 : ¬ p 4 := fun h => c246 u3 h u6
    have u10 : ¬ p 10 := fun h => c318 u4 h u6
    have u11 : ¬ p 85 := fun h => c180 h a0 u7
    have u12 : p 87 := Classical.byContradiction (fun h => c189 u5 h u10)
    have u13 : ¬ p 86 := fun h => c183 h u11 u8
    exact c186 u12 u13 u9
  have c667 : (¬ p 85) → False := by
    intro a0
    have u0 : p 84 := Classical.byContradiction (fun h => c666 h)
    exact c178 a0 u0
  have c668 : (¬ p 86) → False := by
    intro a0
    have u0 : p 85 := Classical.byContradiction (fun h => c667 h)
    exact c181 a0 u0
  have c669 : (¬ p 87) → False := by
    intro a0
    have u0 : p 86 := Classical.byContradiction (fun h => c668 h)
    exact c184 a0 u0
  have c670 : (p 65) → False := by
    intro a0
    have u0 : ¬ p 93 := fun h => c663 h
    have u1 : ¬ p 118 := fun h => c613 h
    have u2 : ¬ p 134 := fun h => c581 h
    have u3 : ¬ p 137 := fun h => c575 h
    have u4 : p 23 := Classical.byContradiction (fun h => c118 a0 h)
    have u5 : p 64 := Classical.byContradiction (fun h => c119 a0 h)
    have u6 : ¬ p 0 := fun h => c204 u0 h u4
    have u7 : ¬ p 6 := fun h => c279 u1 h u4
    have u8 : ¬ p 10 := fun h => c327 u2 h u4
    have u9 : ¬ p 11 := fun h => c336 u3 h u4
    have u10 : p 63 := Classical.byContradiction (fun h => c117 u5 h u7)
    have u11 : ¬ p 62 := fun h => c111 h u8 u9
    exact c114 u10 u11 u6
  have c671 : (p 45) → False := by
    intro a0
    have u0 : ¬ p 97 := fun h => c655 h
    have u1 : ¬ p 113 := fun h => c623 h
    have u2 : ¬ p 116 := fun h => c617 h
    have u3 : ¬ p 123 := fun h => c603 h
    have u4 : p 18 := Classical.byContradiction (fun h => c58 a0 h)
    have u5 : p 44 := Classical.byContradiction (fun h => c59 a0 h)
    have u6 : ¬ p 1 := fun h => c216 u0 h u4
    have u7 : ¬ p 5 := fun h => c264 u1 h u4
    have u8 : ¬ p 6 := fun h => c273 u2 h u4
    have u9 : ¬ p 8 := fun h => c294 u3 h u4
    have u10 : p 43 := Classical.byContradiction (fun h => c57 u5 h u6)
    have u11 : ¬ p 42 := fun h => c51 h u7 u8
    exact c54 u10 u11 u9
  have c672 : (p 53) → (¬ p 10) → False := by
    intro a0 a1
    have u0 : ¬ p 106 := fun h => c637 h
    have u1 : ¬ p 121 := fun h => c607 h
    have u2 : ¬ p 124 := fun h => c601 h
    have u3 : p 20 := Classical.byContradiction (fun h => c82 a0 h)
    have u4 : p 52 := Classical.byContradiction (fun h => c83 a0 h)
    have u5 : ¬ p 3 := fun h => c243 u0 h u3
    have u6 : ¬ p 7 := fun h => c288 u1 h u3
    have u7 : ¬ p 8 := fun h => c297 u2 h u3
    have u8 : p 51 := Classical.byContradiction (fun h => c81 u4 h u5)
    have u9 : ¬ p 50 := fun h => c75 h u6 u7
    exact c78 u8 u9 a1
  have c673 : (p 49) → False := by
    intro a0
    have u0 : ¬ p 101 := fun h => c647 h
    have u1 : ¬ p 117 := fun h => c615 h
    have u2 : ¬ p 120 := fun h => c609 h
    have u3 : ¬ p 128 := fun h => c593 h
    have u4 : p 19 := Classical.byContradiction (fun h => c70 a0 h)
    have u5 : p 48 := Classical.byContradiction (fun h => c71 a0 h)
    have u6 : ¬ p 2 := fun h => c228 u0 h u4
    have u7 : ¬ p 6 := fun h => c276 u1 h u4
    have u8 : ¬ p 7 := fun h => c285 u2 h u4
    have u9 : ¬ p 9 := fun h => c309 u3 h u4
    have u10 : p 47 := Classical.byContradiction (fun h => c69 u5 h u6)
    have u11 : ¬ p 46 := fun h => c63 h u7 u8
    exact c66 u10 u11 u9
  have c674 : (p 57) → (¬ p 11) → False := by
    intro a0 a1
    have u0 : ¬ p 110 := fun h => c629 h
    have u1 : ¬ p 125 := fun h => c599 h
    have u2 : ¬ p 129 := fun h => c591 h
    have u3 : p 21 := Classical.byContradiction (fun h => c94 a0 h)
    have u4 : p 56 := Classical.byContradiction (fun h => c95 a0 h)
    have u5 : ¬ p 4 := fun h => c255 u0 h u3
    have u6 : ¬ p 8 := fun h => c300 u1 h u3
    have u7 : ¬ p 9 := fun h => c312 u2 h u3
    have u8 : p 55 := Classical.byContradiction (fun h => c93 u4 h u5)
    have u9 : ¬ p 54 := fun h => c87 h u6 u7
    exact c90 u8 u9 a1
  have c675 : (¬ p 62) → (p 63) → (p 79) → (¬ p 75) → False := by
    intro a0 a1 a2 a3
    have u0 : ¬ p 92 := fun h => c665 h
    have u1 : ¬ p 49 := fun h => c673 h
    have u2 : ¬ p 45 := fun h => c671 h
    have u3 : ¬ p 10 := fun h => c109 a0 h
    have u4 : p 0 := Classical.byContradiction (fun h => c114 a1 a0 h)
    have u5 : ¬ p 53 := fun h => c672 h u3
    have u6 : ¬ p 17 := fun h => c201 u0 u4 h
    have u7 : p 78 := Classical.byContradiction (fun h => c162 a2 h u5)
    have u8 : ¬ p 41 := fun h => c46 h u6
    have u9 : p 77 := Classical.byContradiction (fun h => c159 u7 h u1)
    have u10 : ¬ p 76 := fun h => c153 h a3 u8
    exact c156 u9 u10 u2
  have c676 : (p 41) → False := by
    intro a0
    have u0 : ¬ p 92 := fun h => c665 h
    have u1 : ¬ p 112 := fun h => c625 h
    have u2 : ¬ p 119 := fun h => c611 h
    have u3 : ¬ p 109 := fun h => c631 h
    have u4 : p 17 := Classical.byContradiction (fun h => c46 a0 h)
    have u5 : p 40 := Classical.byContradiction (fun h => c47 a0 h)
    have u6 : ¬ p 0 := fun h => c201 u0 h u4
    have u7 : ¬ p 5 := fun h => c261 u1 h u4
    have u8 : ¬ p 7 := fun h => c282 u2 h u4
    have u9 : p 39 := Classical.byContradiction (fun h => c45 u5 h u6)
    have u10 : p 38 := Classical.byContradiction (fun h => c42 u9 h u8)
    have u11 : ¬ p 4 := fun h => c252 u3 h u4
    exact c39 u10 u11 u7
  have c677 : (p 53) → False := by
    intro a0
    have u0 : ¬ p 132 := fun h => c585 h
    have u1 : p 20 := Classical.byContradiction (fun h => c82 a0 h)
    have u2 : p 10 := Classical.byContradiction (fun h => c672 a0 h)
    exact c321 u0 u2 u1
  have c678 : (p 57) → False := by
    intro a0
    have u0 : ¬ p 136 := fun h => c577 h
    have u1 : p 21 := Classical.byContradiction (fun h => c94 a0 h)
    have u2 : p 11 := Classical.byContradiction (fun h => c674 a0 h)
    exact c333 u0 u2 u1
  have c679 : (p 29) → (¬ p 0) → False := by
    intro a0 a1
    have u0 : ¬ p 95 := fun h => c659 h
    have u1 : ¬ p 103 := fun h => c643 h
    have u2 : ¬ p 127 := fun h => c595 h
    have u3 : p 13 := Classical.byContradiction (fun h => c10 a0 h)
    have u4 : p 28 := Classical.byContradiction (fun h => c11 a0 h)
    have u5 : ¬ p 1 := fun h => c210 u0 h u3
    have u6 : ¬ p 3 := fun h => c234 u1 h u3
    have u7 : ¬ p 9 := fun h => c306 u2 h u3
    have u8 : ¬ p 26 := fun h => c3 h a1 u5
    have u9 : ¬ p 27 := fun h => c6 h u8 u6
    exact c9 u4 u9 u7
  have c680 : (p 17) → (p 74) → False := by
    intro a0 a1
    have u0 : ¬ p 92 := fun h => c665 h
    have u1 : ¬ p 112 := fun h => c625 h
    have u2 : ¬ p 100 := fun h => c649 h
    have u3 : ¬ p 104 := fun h => c641 h
    have u4 : ¬ p 135 := fun h => c579 h
    have u5 : ¬ p 0 := fun h => c201 u0 h a0
    have u6 : ¬ p 5 := fun h => c261 u1 h a0
    have u7 : ¬ p 29 := fun h => c679 h u5
    have u8 : p 33 := Classical.byContradiction (fun h => c147 a1 u7 h)
    have u9 : p 15 := Classical.byContradiction (fun h => c22 u8 h)
    have u10 : p 32 := Classical.byContradiction (fun h => c23 u8 h)
    have u11 : ¬ p 2 := fun h => c225 u2 h u9
    have u12 : ¬ p 3 := fun h => c237 u3 h u9
    have u13 : ¬ p 11 := fun h => c330 u4 h u9
    have u14 : p 31 := Classical.byContradiction (fun h => c21 u10 h u13)
    have u15 : ¬ p 30 := fun h => c15 h u11 u12
    exact c18 u14 u15 u6
  have c681 : (p 33) → False := by
    intro a0
    have u0 : ¬ p 100 := fun h => c649 h
    have u1 : ¬ p 104 := fun h => c641 h
    have u2 : ¬ p 111 := fun h => c627 h
    have u3 : ¬ p 135 := fun h => c579 h
    have u4 : p 15 := Classical.byContradiction (fun h => c22 a0 h)
    have u5 : p 32 := Classical.byContradiction (fun h => c23 a0 h)
    have u6 : ¬ p 2 := fun h => c225 u0 h u4
    have u7 : ¬ p 3 := fun h => c237 u1 h u4
    have u8 : ¬ p 5 := fun h => c258 u2 h u4
    have u9 : ¬ p 11 := fun h => c330 u3 h u4
    have u10 : p 31 := Classical.byContradiction (fun h => c21 u5 h u9)
    have u11 : ¬ p 30 := fun h => c15 h u6 u7
    exact c18 u10 u11 u8
  have c682 : (p 29) → False := by
    intro a0
    have u0 : ¬ p 91 := fun h => c664 h
    have u1 : p 13 := Classical.byContradiction (fun h => c10 a0 h)
    have u2 : p 0 := Classical.byContradiction (fun h => c679 a0 h)
    exact c198 u0 u2 u1
  have c683 : (p 74) → False := by
    intro a0
    have u0 : ¬ p 29 := fun h => c682 h
    have u1 : ¬ p 33 := fun h => c681 h
    exact c147 a0 u0 u1
  have c684 : (p 37) → (¬ p 3) → False := by
    intro a0 a1
    have u0 : ¬ p 108 := fun h => c633 h
    have u1 : ¬ p 115 := fun h => c619 h
    have u2 : ¬ p 139 := fun h => c571 h
    have u3 : p 16 := Classical.byContradiction (fun h => c34 a0 h)
    have u4 : p 36 := Classical.byContradiction (fun h => c35 a0 h)
    have u5 : ¬ p 4 := fun h => c249 u0 h u3
    have u6 : ¬ p 6 := fun h => c270 u1 h u3
    have u7 : ¬ p 12 := fun h => c342 u2 h u3
    have u8 : p 35 := Classical.byContradiction (fun h => c33 u4 h u7)
    have u9 : ¬ p 34 := fun h => c27 h a1 u5
    exact c30 u8 u9 u6
  have c685 : (p 69) → (¬ p 67) → False := by
    intro a0 a1
    have u0 : ¬ p 122 := fun h => c605 h
    have u1 : p 24 := Classical.byContradiction (fun h => c130 a0 h)
    have u2 : p 68 := Classical.byContradiction (fun h => c131 a0 h)
    have u3 : ¬ p 7 := fun h => c291 u0 h u1
    exact c129 u2 a1 u3
  have c686 : (p 61) → (¬ p 9) → (¬ p 5) → (¬ p 12) → False := by
    intro a0 a1 a2 a3
    have u0 : ¬ p 133 := fun h => c583 h
    have u1 : p 22 := Classical.byContradiction (fun h => c106 a0 h)
    have u2 : p 60 := Classical.byContradiction (fun h => c107 a0 h)
    have u3 : ¬ p 10 := fun h => c324 u0 h u1
    have u4 : p 59 := Classical.byContradiction (fun h => c105 u2 h a2)
    have u5 : ¬ p 58 := fun h => c99 h a1 u3
    exact c102 u4 u5 a3
  have c687 : (p 69) → (¬ p 66) → False := by
    intro a0 a1
    have u0 : ¬ p 98 := fun h => c653 h
    have u1 : p 24 := Classical.byContradiction (fun h => c130 a0 h)
    have u2 : p 67 := Classical.byContradiction (fun h => c685 a0 h)
    have u3 : ¬ p 1 := fun h => c219 u0 h u1
    exact c126 u2 a1 u3
  have c688 : (p 61) → (¬ p 12) → False := by
    intro a0 a1
    have u0 : ¬ p 130 := fun h => c589 h
    have u1 : ¬ p 114 := fun h => c621 h
    have u2 : p 22 := Classical.byContradiction (fun h => c106 a0 h)
    have u3 : ¬ p 9 := fun h => c315 u0 h u2
    have u4 : ¬ p 5 := fun h => c267 u1 h u2
    exact c686 a0 u3 u4 a1
  have c689 : (¬ p 12) → (¬ p 80) → (p 83) → False := by
    intro a0 a1 a2
    have u0 : ¬ p 65 := fun h => c670 h
    have u1 : ¬ p 138 := fun h => c573 h
    have u2 : ¬ p 61 := fun h => c688 h a0
    have u3 : ¬ p 81 := fun h => c168 h a1 u2
    have u4 : ¬ p 82 := fun h => c171 h u3 u0
    have u5 : p 69 := Classical.byContradiction (fun h => c174 a2 u4 h)
    have u6 : p 24 := Classical.byContradiction (fun h => c130 u5 h)
    have u7 : p 66 := Classical.byContradiction (fun h => c687 u5 h)
    have u8 : ¬ p 11 := fun h => c339 u1 h u6
    exact c123 u7 u8 a0
  have c690 : (¬ p 80) → (p 83) → False := by
    intro a0 a1
    have u0 : ¬ p 65 := fun h => c670 h
    have u1 : ¬ p 141 := fun h => c565 h
    have u2 : ¬ p 140 := fun h => c569 h
    have u3 : p 12 := Classical.byContradiction (fun h => c689 h a0 a1)
    have u4 : ¬ p 22 := fun h => c345 u2 u3 h
    have u5 : ¬ p 24 := fun h => c348 u1 u3 h
    have u6 : ¬ p 61 := fun h => c106 h u4
    have u7 : ¬ p 69 := fun h => c130 h u5
    have u8 : ¬ p 81 := fun h => c168 h a0 u6
    have u9 : p 82 := Classical.byContradiction (fun h => c174 a1 h u7)
    exact c171 u9 u8 u0
  have c691 : (p 37) → False := by
    intro a0
    have u0 : ¬ p 105 := fun h => c639 h
    have u1 : p 16 := Classical.byContradiction (fun h => c34 a0 h)
    have u2 : p 3 := Classical.byContradiction (fun h => c684 a0 h)
    exact c240 u0 u2 u1
  have c692 : (p 75) → False := by
    intro a0
    have u0 : ¬ p 37 := fun h => c691 h
    have u1 : ¬ p 74 := fun h => c683 h
    exact c150 a0 u1 u0
  have c693 : (p 76) → False := by
    intro a0
    have u0 : ¬ p 75 := fun h => c692 h
    have u1 : ¬ p 41 := fun h => c676 h
    exact c153 a0 u0 u1
  have c694 : (p 77) → False := by
    intro a0
    have u0 : ¬ p 76 := fun h => c693 h
    have u1 : ¬ p 45 := fun h => c671 h
    exact c156 a0 u0 u1
  have c695 : (p 78) → False := by
    intro a0
    have u0 : ¬ p 77 := fun h => c694 h
    have u1 : ¬ p 49 := fun h => c673 h
    exact c159 a0 u0 u1
  have c696 : (p 79) → False := by
    intro a0
    have u0 : ¬ p 78 := fun h => c695 h
    have u1 : ¬ p 53 := fun h => c677 h
    exact c162 a0 u0 u1
  have c697 : (p 80) → False := by
    intro a0
    have u0 : ¬ p 79 := fun h => c696 h
    have u1 : ¬ p 57 := fun h => c678 h
    exact c165 a0 u0 u1
  have c698 : (p 83) → False := by
    intro a0
    have u0 : ¬ p 80 := fun h => c697 h
    exact c690 u0 a0
  have c699 : (p 82) → False := by
    intro a0
    have u0 : ¬ p 83 := fun h => c698 h
    exact c172 u0 a0
  have c700 : (p 69) → False := by
    intro a0
    have u0 : ¬ p 83 := fun h => c698 h
    exact c173 u0 a0
  have c701 : (¬ p 73) → False := by
    intro a0
    have u0 : ¬ p 83 := fun h => c698 h
    have u1 : p 84 := Classical.byContradiction (fun h => c666 h)
    exact c177 u1 u0 a0
  have c702 : (p 81) → False := by
    intro a0
    have u0 : ¬ p 82 := fun h => c699 h
    exact c169 u0 a0
  have c703 : (¬ p 25) → False := by
    intro a0
    have u0 : p 73 := Classical.byContradiction (fun h => c701 h)
    exact c142 u0 a0
  have c704 : (¬ p 72) → False := by
    intro a0
    have u0 : p 73 := Classical.byContradiction (fun h => c701 h)
    exact c143 u0 a0
  have c705 : (p 61) → False := by
    intro a0
    have u0 : ¬ p 81 := fun h => c702 h
    exact c167 u0 a0
  have c706 : (p 12) → False := by
    intro a0
    have u0 : p 25 := Classical.byContradiction (fun h => c703 h)
    have u1 : ¬ p 142 := fun h => c562 h
    exact c351 u1 a0 u0
  have c707 : (p 0) → False := by
    intro a0
    have u0 : p 25 := Classical.byContradiction (fun h => c703 h)
    have u1 : ¬ p 94 := fun h => c661 h
    exact c207 u1 a0 u0
  have c708 : (p 2) → False := by
    intro a0
    have u0 : p 25 := Classical.byContradiction (fun h => c703 h)
    have u1 : ¬ p 102 := fun h => c645 h
    exact c231 u1 a0 u0
  have c709 : (p 8) → False := by
    intro a0
    have u0 : p 25 := Classical.byContradiction (fun h => c703 h)
    have u1 : ¬ p 126 := fun h => c597 h
    exact c303 u1 a0 u0
  have c710 : (p 70) → False := by
    intro a0
    have u0 : ¬ p 12 := fun h => c706 h
    have u1 : ¬ p 0 := fun h => c707 h
    exact c135 a0 u0 u1
  have c711 : (¬ p 71) → False := by
    intro a0
    have u0 : ¬ p 8 := fun h => c709 h
    have u1 : p 72 := Classical.byContradiction (fun h => c704 h)
    exact c141 u1 a0 u0
  have c712 : False := by
    have u0 : p 71 := Classical.byContradiction (fun h => c711 h)
    have u1 : ¬ p 70 := fun h => c710 h
    have u2 : ¬ p 2 := fun h => c708 h
    exact c138 u0 u1 u2
  exact c712

#print axioms PEqualNP.Outside.L_meta_2602_aux.rup_unsat
