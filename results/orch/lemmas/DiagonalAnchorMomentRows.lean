import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

namespace PEqualNP.Outside.L_gct_231_aux.DiagonalAnchorMoment

def integerRow0 : Fin 35 → ℤ :=
  ![-1152, -36864, -516096, -7077888, -96804864, -313344, -9068544, -126443520, -1744109568, -66539520, -1864433664, -25745817600, -13058703360, -360054521856, -2476120080384, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def integerRow1 : Fin 35 → ℤ :=
  ![0, -1152, 0, 0, 0, -36864, -516096, -7077888, -96804864, 0, 0, 0, 0, 0, 0, -313344, -9068544, -126443520, -1744109568, -66539520, -1864433664, -25745817600, -13058703360, -360054521856, -2476120080384, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def integerRow2 : Fin 35 → ℤ :=
  ![0, 0, -1152, 0, 0, 0, -36864, 0, 0, -516096, -7077888, -96804864, 0, 0, 0, 0, -313344, 0, 0, -9068544, -126443520, -1744109568, 0, 0, 0, -66539520, -1864433664, -25745817600, -13058703360, -360054521856, -2476120080384, 0, 0, 0, 0]

def integerRow3 : Fin 35 → ℤ :=
  ![0, 0, 0, -1152, 0, 0, 0, -36864, 0, 0, -516096, 0, -7077888, -96804864, 0, 0, 0, -313344, 0, 0, -9068544, 0, -126443520, -1744109568, 0, 0, -66539520, 0, -1864433664, -25745817600, 0, -13058703360, -360054521856, -2476120080384, 0]

def integerRow4 : Fin 35 → ℤ :=
  ![0, 0, 0, 0, -1152, 0, 0, 0, -36864, 0, 0, -516096, 0, -7077888, -96804864, 0, 0, 0, -313344, 0, 0, -9068544, 0, -126443520, -1744109568, 0, 0, -66539520, 0, -1864433664, -25745817600, 0, -13058703360, -360054521856, -2476120080384]

def integerRow5 : Fin 35 → ℤ :=
  ![-2304, -82944, -1253376, -18063360, -255541248, -774144, -23814144, -345931776, -4911169536, -184246272, -5357961216, -76004720640, -38890635264, -1100930088960, -7773071081472, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def integerRow6 : Fin 35 → ℤ :=
  ![0, -2304, 0, 0, 0, -82944, -1253376, -18063360, -255541248, 0, 0, 0, 0, 0, 0, -774144, -23814144, -345931776, -4911169536, -184246272, -5357961216, -76004720640, -38890635264, -1100930088960, -7773071081472, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def integerRow7 : Fin 35 → ℤ :=
  ![0, 0, -2304, 0, 0, 0, -82944, 0, 0, -1253376, -18063360, -255541248, 0, 0, 0, 0, -774144, 0, 0, -23814144, -345931776, -4911169536, 0, 0, 0, -184246272, -5357961216, -76004720640, -38890635264, -1100930088960, -7773071081472, 0, 0, 0, 0]

def integerRow8 : Fin 35 → ℤ :=
  ![0, 0, 0, -2304, 0, 0, 0, -82944, 0, 0, -1253376, 0, -18063360, -255541248, 0, 0, 0, -774144, 0, 0, -23814144, 0, -345931776, -4911169536, 0, 0, -184246272, 0, -5357961216, -76004720640, 0, -38890635264, -1100930088960, -7773071081472, 0]

def integerRow9 : Fin 35 → ℤ :=
  ![0, 0, 0, 0, -2304, 0, 0, 0, -82944, 0, 0, -1253376, 0, -18063360, -255541248, 0, 0, 0, -774144, 0, 0, -23814144, 0, -345931776, -4911169536, 0, 0, -184246272, 0, -5357961216, -76004720640, 0, -38890635264, -1100930088960, -7773071081472]

def integerRow10 : Fin 35 → ℤ :=
  ![-4224, -172032, -2826240, -43118592, -634822656, -1751040, -57360384, -871759872, -12789743616, -466698240, -14092075008, -205596131328, -105696755712, -3067645132800, -22158905573376, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def integerRow11 : Fin 35 → ℤ :=
  ![0, -4224, 0, 0, 0, -172032, -2826240, -43118592, -634822656, 0, 0, 0, 0, 0, 0, -1751040, -57360384, -871759872, -12789743616, -466698240, -14092075008, -205596131328, -105696755712, -3067645132800, -22158905573376, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def integerRow12 : Fin 35 → ℤ :=
  ![0, 0, -4224, 0, 0, 0, -172032, 0, 0, -2826240, -43118592, -634822656, 0, 0, 0, 0, -1751040, 0, 0, -57360384, -871759872, -12789743616, 0, 0, 0, -466698240, -14092075008, -205596131328, -105696755712, -3067645132800, -22158905573376, 0, 0, 0, 0]

def integerRow13 : Fin 35 → ℤ :=
  ![0, 0, 0, -4224, 0, 0, 0, -172032, 0, 0, -2826240, 0, -43118592, -634822656, 0, 0, 0, -1751040, 0, 0, -57360384, 0, -871759872, -12789743616, 0, 0, -466698240, 0, -14092075008, -205596131328, 0, -105696755712, -3067645132800, -22158905573376, 0]

def integerRow14 : Fin 35 → ℤ :=
  ![0, 0, 0, 0, -4224, 0, 0, 0, -172032, 0, 0, -2826240, 0, -43118592, -634822656, 0, 0, 0, -1751040, 0, 0, -57360384, 0, -871759872, -12789743616, 0, 0, -466698240, 0, -14092075008, -205596131328, 0, -105696755712, -3067645132800, -22158905573376]

def integerRow15 : Fin 35 → ℤ :=
  ![-5376, -267264, -5074944, -85426176, -1344946176, -3084288, -112361472, -1845608448, -28615409664, -990216192, -31792103424, -485228937216, -250787069952, -7560124956672, -56448490143744, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def integerRow16 : Fin 35 → ℤ :=
  ![0, -5376, 0, 0, 0, -267264, -5074944, -85426176, -1344946176, 0, 0, 0, 0, 0, 0, -3084288, -112361472, -1845608448, -28615409664, -990216192, -31792103424, -485228937216, -250787069952, -7560124956672, -56448490143744, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def integerRow17 : Fin 35 → ℤ :=
  ![0, 0, -5376, 0, 0, 0, -267264, 0, 0, -5074944, -85426176, -1344946176, 0, 0, 0, 0, -3084288, 0, 0, -112361472, -1845608448, -28615409664, 0, 0, 0, -990216192, -31792103424, -485228937216, -250787069952, -7560124956672, -56448490143744, 0, 0, 0, 0]

def integerRow18 : Fin 35 → ℤ :=
  ![0, 0, 0, -5376, 0, 0, 0, -267264, 0, 0, -5074944, 0, -85426176, -1344946176, 0, 0, 0, -3084288, 0, 0, -112361472, 0, -1845608448, -28615409664, 0, 0, -990216192, 0, -31792103424, -485228937216, 0, -250787069952, -7560124956672, -56448490143744, 0]

def integerRow19 : Fin 35 → ℤ :=
  ![0, 0, 0, 0, -5376, 0, 0, 0, -267264, 0, 0, -5074944, 0, -85426176, -1344946176, 0, 0, 0, -3084288, 0, 0, -112361472, 0, -1845608448, -28615409664, 0, 0, -990216192, 0, -31792103424, -485228937216, 0, -250787069952, -7560124956672, -56448490143744]

def integerRow20 : Fin 35 → ℤ :=
  ![-1152, -46080, -746496, -11280384, -165076992, -465408, -15114240, -228335616, -3338993664, -122499072, -3691708416, -53859483648, -27734851584, -807306264576, -5862729056256, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def integerRow21 : Fin 35 → ℤ :=
  ![0, -1152, 0, 0, 0, -46080, -746496, -11280384, -165076992, 0, 0, 0, 0, 0, 0, -465408, -15114240, -228335616, -3338993664, -122499072, -3691708416, -53859483648, -27734851584, -807306264576, -5862729056256, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def integerRow22 : Fin 35 → ℤ :=
  ![0, 0, -1152, 0, 0, 0, -46080, 0, 0, -746496, -11280384, -165076992, 0, 0, 0, 0, -465408, 0, 0, -15114240, -228335616, -3338993664, 0, 0, 0, -122499072, -3691708416, -53859483648, -27734851584, -807306264576, -5862729056256, 0, 0, 0, 0]

def integerRow23 : Fin 35 → ℤ :=
  ![0, 0, 0, -1152, 0, 0, 0, -46080, 0, 0, -746496, 0, -11280384, -165076992, 0, 0, 0, -465408, 0, 0, -15114240, 0, -228335616, -3338993664, 0, 0, -122499072, 0, -3691708416, -53859483648, 0, -27734851584, -807306264576, -5862729056256, 0]

def integerRow24 : Fin 35 → ℤ :=
  ![0, 0, 0, 0, -1152, 0, 0, 0, -46080, 0, 0, -746496, 0, -11280384, -165076992, 0, 0, 0, -465408, 0, 0, -15114240, 0, -228335616, -3338993664, 0, 0, -122499072, 0, -3691708416, -53859483648, 0, -27734851584, -807306264576, -5862729056256]

def integerRow25 : Fin 35 → ℤ :=
  ![-1536, -69888, -1265664, -20766720, -322240512, -780288, -27838464, -451915776, -6961668096, -244408320, -7838957568, -119706353664, -62242258944, -1887321194496, -14229972713472, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def integerRow26 : Fin 35 → ℤ :=
  ![0, -1536, 0, 0, 0, -69888, -1265664, -20766720, -322240512, 0, 0, 0, 0, 0, 0, -780288, -27838464, -451915776, -6961668096, -244408320, -7838957568, -119706353664, -62242258944, -1887321194496, -14229972713472, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def integerRow27 : Fin 35 → ℤ :=
  ![0, 0, -1536, 0, 0, 0, -69888, 0, 0, -1265664, -20766720, -322240512, 0, 0, 0, 0, -780288, 0, 0, -27838464, -451915776, -6961668096, 0, 0, 0, -244408320, -7838957568, -119706353664, -62242258944, -1887321194496, -14229972713472, 0, 0, 0, 0]

def integerRow28 : Fin 35 → ℤ :=
  ![0, 0, 0, -1536, 0, 0, 0, -69888, 0, 0, -1265664, 0, -20766720, -322240512, 0, 0, 0, -780288, 0, 0, -27838464, 0, -451915776, -6961668096, 0, 0, -244408320, 0, -7838957568, -119706353664, 0, -62242258944, -1887321194496, -14229972713472, 0]

def integerRow29 : Fin 35 → ℤ :=
  ![0, 0, 0, 0, -1536, 0, 0, 0, -69888, 0, 0, -1265664, 0, -20766720, -322240512, 0, 0, 0, -780288, 0, 0, -27838464, 0, -451915776, -6961668096, 0, 0, -244408320, 0, -7838957568, -119706353664, 0, -62242258944, -1887321194496, -14229972713472]

def integerRow30 : Fin 35 → ℤ :=
  ![576, -15360, -921600, -22505472, -426848256, -522240, -30056448, -622018560, -11009359872, -344850432, -12987531264, -219038220288, -116308230144, -3811976478720, -30689210597376, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def integerRow31 : Fin 35 → ℤ :=
  ![0, 576, 0, 0, 0, -15360, -921600, -22505472, -426848256, 0, 0, 0, 0, 0, 0, -522240, -30056448, -622018560, -11009359872, -344850432, -12987531264, -219038220288, -116308230144, -3811976478720, -30689210597376, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def integerRow32 : Fin 35 → ℤ :=
  ![0, 0, 576, 0, 0, 0, -15360, 0, 0, -921600, -22505472, -426848256, 0, 0, 0, 0, -522240, 0, 0, -30056448, -622018560, -11009359872, 0, 0, 0, -344850432, -12987531264, -219038220288, -116308230144, -3811976478720, -30689210597376, 0, 0, 0, 0]

def integerRow33 : Fin 35 → ℤ :=
  ![0, 0, 0, 576, 0, 0, 0, -15360, 0, 0, -921600, 0, -22505472, -426848256, 0, 0, 0, -522240, 0, 0, -30056448, 0, -622018560, -11009359872, 0, 0, -344850432, 0, -12987531264, -219038220288, 0, -116308230144, -3811976478720, -30689210597376, 0]

def integerRow34 : Fin 35 → ℤ :=
  ![0, 0, 0, 0, 576, 0, 0, 0, -15360, 0, 0, -921600, 0, -22505472, -426848256, 0, 0, 0, -522240, 0, 0, -30056448, 0, -622018560, -11009359872, 0, 0, -344850432, 0, -12987531264, -219038220288, 0, -116308230144, -3811976478720, -30689210597376]

def integerMatrix : Matrix (Fin 35) (Fin 35) ℤ :=
  ![integerRow0, integerRow1, integerRow2, integerRow3, integerRow4, integerRow5, integerRow6, integerRow7, integerRow8, integerRow9, integerRow10, integerRow11, integerRow12, integerRow13, integerRow14, integerRow15, integerRow16, integerRow17, integerRow18, integerRow19, integerRow20, integerRow21, integerRow22, integerRow23, integerRow24, integerRow25, integerRow26, integerRow27, integerRow28, integerRow29, integerRow30, integerRow31, integerRow32, integerRow33, integerRow34]

def inverseRow0 : Fin 35 → (ZMod 461) :=
  ![24, 343, 244, 30, 337, 186, 125, 156, 172, 351, 335, 155, 400, 337, 144, 221, 156, 172, 385, 323, 132, 299, 138, 185, 294, 226, 70, 390, 247, 156, 181, 152, 108, 441, 19]

def inverseRow1 : Fin 35 → (ZMod 461) :=
  ![97, 188, 331, 71, 362, 27, 422, 44, 134, 275, 29, 117, 121, 239, 225, 355, 98, 430, 217, 449, 319, 344, 369, 292, 460, 260, 235, 256, 380, 129, 242, 285, 434, 29, 273]

def inverseRow2 : Fin 35 → (ZMod 461) :=
  ![192, 200, 350, 287, 150, 252, 332, 311, 79, 450, 409, 48, 53, 237, 455, 137, 137, 185, 315, 15, 239, 136, 195, 222, 405, 19, 149, 326, 449, 217, 52, 59, 312, 261, 160]

def inverseRow3 : Fin 35 → (ZMod 461) :=
  ![225, 159, 460, 110, 263, 191, 224, 319, 351, 313, 451, 378, 99, 95, 203, 125, 450, 75, 196, 113, 359, 8, 360, 278, 412, 45, 377, 419, 365, 336, 72, 83, 420, 344, 368]

def inverseRow4 : Fin 35 → (ZMod 461) :=
  ![439, 153, 302, 438, 35, 205, 84, 118, 366, 6, 418, 453, 246, 249, 122, 16, 213, 77, 399, 414, 130, 235, 366, 316, 336, 280, 1, 422, 154, 311, 80, 328, 413, 360, 417]

def inverseRow5 : Fin 35 → (ZMod 461) :=
  ![10, 331, 62, 66, 204, 174, 351, 147, 163, 4, 14, 64, 176, 217, 121, 313, 448, 142, 396, 252, 132, 88, 363, 448, 239, 235, 437, 185, 58, 285, 328, 180, 445, 269, 51]

def inverseRow6 : Fin 35 → (ZMod 461) :=
  ![193, 424, 443, 372, 202, 370, 67, 206, 140, 437, 410, 93, 48, 95, 357, 266, 377, 406, 459, 274, 389, 145, 161, 154, 337, 228, 420, 106, 327, 456, 136, 168, 122, 294, 340]

def inverseRow7 : Fin 35 → (ZMod 461) :=
  ![237, 278, 378, 146, 139, 16, 328, 306, 447, 106, 113, 6, 234, 32, 293, 338, 390, 108, 20, 184, 417, 402, 127, 442, 36, 60, 175, 106, 271, 33, 137, 241, 109, 119, 386]

def inverseRow8 : Fin 35 → (ZMod 461) :=
  ![168, 112, 435, 40, 34, 362, 37, 21, 163, 10, 48, 264, 84, 100, 294, 370, 299, 193, 22, 6, 418, 122, 325, 364, 394, 236, 135, 446, 116, 37, 447, 54, 136, 368, 33]

def inverseRow9 : Fin 35 → (ZMod 461) :=
  ![184, 155, 333, 421, 173, 407, 385, 431, 137, 183, 40, 326, 290, 247, 178, 189, 121, 440, 155, 210, 28, 86, 319, 245, 78, 197, 140, 415, 253, 434, 332, 261, 214, 241, 283]

def inverseRow10 : Fin 35 → (ZMod 461) :=
  ![333, 179, 234, 227, 303, 234, 312, 398, 382, 333, 201, 242, 235, 416, 313, 32, 294, 446, 342, 265, 349, 5, 43, 148, 138, 261, 197, 315, 145, 288, 5, 37, 363, 89, 67]

def inverseRow11 : Fin 35 → (ZMod 461) :=
  ![230, 399, 262, 372, 143, 272, 316, 84, 371, 370, 429, 154, 169, 303, 46, 6, 442, 188, 108, 416, 307, 389, 99, 0, 136, 313, 439, 86, 359, 6, 52, 444, 25, 384, 270]

def inverseRow12 : Fin 35 → (ZMod 461) :=
  ![387, 322, 17, 246, 213, 291, 67, 361, 371, 365, 251, 71, 41, 36, 390, 397, 33, 457, 236, 378, 400, 453, 151, 24, 347, 444, 398, 458, 412, 367, 248, 70, 30, 376, 136]

def inverseRow13 : Fin 35 → (ZMod 461) :=
  ![11, 287, 22, 271, 334, 311, 154, 368, 119, 237, 389, 97, 125, 122, 238, 13, 350, 292, 226, 156, 237, 139, 122, 407, 63, 262, 13, 306, 115, 170, 188, 135, 250, 316, 430]

def inverseRow14 : Fin 35 → (ZMod 461) :=
  ![326, 141, 396, 416, 162, 389, 233, 419, 336, 136, 118, 117, 452, 39, 243, 365, 452, 203, 205, 277, 321, 173, 450, 387, 319, 420, 221, 248, 148, 395, 405, 280, 130, 180, 360]

def inverseRow15 : Fin 35 → (ZMod 461) :=
  ![86, 397, 167, 35, 390, 413, 4, 458, 12, 260, 432, 144, 383, 268, 172, 118, 318, 227, 25, 264, 392, 254, 62, 405, 34, 369, 226, 230, 226, 363, 178, 121, 350, 410, 107]

def inverseRow16 : Fin 35 → (ZMod 461) :=
  ![6, 327, 3, 198, 243, 411, 48, 53, 422, 340, 104, 142, 234, 448, 242, 282, 351, 185, 330, 417, 329, 381, 24, 293, 416, 331, 307, 187, 309, 250, 291, 354, 413, 125, 177]

def inverseRow17 : Fin 35 → (ZMod 461) :=
  ![296, 340, 210, 6, 5, 112, 354, 279, 260, 178, 47, 308, 7, 402, 140, 322, 421, 229, 454, 260, 415, 92, 321, 441, 344, 33, 401, 102, 156, 239, 237, 180, 259, 200, 259]

def inverseRow18 : Fin 35 → (ZMod 461) :=
  ![386, 424, 64, 171, 148, 375, 0, 394, 227, 72, 417, 99, 429, 288, 276, 175, 78, 63, 137, 65, 239, 303, 428, 161, 4, 365, 316, 368, 313, 47, 424, 105, 434, 288, 182]

def inverseRow19 : Fin 35 → (ZMod 461) :=
  ![217, 412, 9, 188, 219, 447, 85, 397, 185, 390, 317, 136, 124, 14, 16, 375, 258, 114, 415, 397, 350, 251, 458, 314, 314, 151, 428, 80, 56, 376, 83, 457, 2, 238, 96]

def inverseRow20 : Fin 35 → (ZMod 461) :=
  ![336, 180, 161, 73, 369, 190, 59, 392, 129, 6, 74, 320, 84, 152, 197, 49, 15, 377, 110, 52, 103, 275, 187, 397, 1, 195, 382, 342, 160, 274, 392, 101, 28, 254, 397]

def inverseRow21 : Fin 35 → (ZMod 461) :=
  ![94, 169, 250, 273, 373, 37, 175, 89, 287, 138, 80, 277, 394, 191, 379, 343, 434, 323, 255, 275, 338, 405, 190, 124, 66, 111, 76, 309, 369, 210, 25, 135, 277, 446, 321]

def inverseRow22 : Fin 35 → (ZMod 461) :=
  ![93, 231, 20, 327, 87, 230, 297, 349, 234, 226, 424, 96, 271, 428, 200, 102, 409, 179, 15, 72, 402, 265, 154, 328, 181, 450, 261, 456, 270, 91, 410, 189, 339, 33, 63]

def inverseRow23 : Fin 35 → (ZMod 461) :=
  ![211, 132, 362, 356, 408, 72, 271, 208, 387, 10, 323, 230, 225, 300, 157, 77, 62, 180, 269, 105, 241, 158, 263, 402, 204, 116, 21, 199, 185, 246, 286, 40, 177, 122, 54]

def inverseRow24 : Fin 35 → (ZMod 461) :=
  ![15, 19, 442, 370, 67, 226, 460, 404, 385, 444, 7, 7, 139, 441, 112, 24, 180, 125, 435, 140, 289, 155, 254, 242, 404, 438, 214, 444, 83, 220, 343, 329, 106, 210, 311]

def inverseRow25 : Fin 35 → (ZMod 461) :=
  ![319, 417, 369, 147, 186, 101, 25, 34, 237, 325, 203, 301, 51, 90, 99, 447, 246, 303, 190, 95, 20, 70, 373, 239, 176, 52, 194, 93, 181, 201, 120, 421, 328, 210, 178]

def inverseRow26 : Fin 35 → (ZMod 461) :=
  ![174, 232, 334, 173, 347, 155, 365, 363, 124, 264, 333, 413, 167, 348, 127, 327, 19, 96, 143, 64, 442, 263, 156, 205, 170, 253, 50, 382, 265, 427, 30, 319, 59, 320, 278]

def inverseRow27 : Fin 35 → (ZMod 461) :=
  ![286, 13, 422, 43, 413, 70, 384, 81, 76, 341, 432, 240, 318, 383, 130, 410, 195, 226, 370, 360, 217, 162, 142, 376, 395, 377, 48, 159, 70, 232, 66, 285, 157, 227, 181]

def inverseRow28 : Fin 35 → (ZMod 461) :=
  ![339, 452, 219, 372, 60, 86, 112, 401, 286, 22, 460, 321, 154, 203, 409, 323, 440, 395, 206, 377, 407, 453, 297, 291, 377, 134, 245, 381, 409, 113, 437, 101, 310, 166, 163]

def inverseRow29 : Fin 35 → (ZMod 461) :=
  ![419, 19, 454, 392, 123, 221, 95, 162, 350, 86, 252, 50, 446, 447, 82, 311, 236, 378, 12, 231, 158, 407, 399, 235, 432, 241, 291, 281, 248, 150, 209, 164, 449, 408, 71]

def inverseRow30 : Fin 35 → (ZMod 461) :=
  ![112, 198, 254, 434, 435, 201, 273, 33, 47, 444, 391, 447, 338, 396, 242, 340, 178, 2, 119, 250, 167, 1, 54, 353, 402, 133, 456, 383, 147, 5, 74, 175, 3, 353, 363]

def inverseRow31 : Fin 35 → (ZMod 461) :=
  ![358, 445, 300, 187, 99, 246, 294, 356, 76, 429, 301, 307, 305, 14, 180, 17, 251, 297, 215, 40, 236, 35, 213, 243, 234, 172, 435, 312, 258, 126, 233, 374, 245, 39, 48]

def inverseRow32 : Fin 35 → (ZMod 461) :=
  ![214, 151, 399, 341, 186, 279, 456, 228, 18, 98, 211, 227, 310, 442, 47, 96, 438, 238, 371, 293, 99, 95, 359, 10, 40, 284, 425, 214, 126, 165, 179, 43, 263, 230, 460]

def inverseRow33 : Fin 35 → (ZMod 461) :=
  ![54, 123, 357, 336, 257, 374, 455, 404, 49, 291, 123, 275, 51, 164, 227, 85, 48, 392, 199, 185, 190, 460, 216, 318, 183, 404, 213, 25, 36, 107, 454, 84, 11, 301, 227]

def inverseRow34 : Fin 35 → (ZMod 461) :=
  ![417, 198, 71, 386, 426, 314, 432, 433, 73, 357, 434, 135, 308, 196, 126, 404, 97, 247, 230, 385, 246, 13, 360, 236, 390, 353, 426, 433, 385, 275, 181, 39, 253, 78, 394]

def modularInverse : Matrix (Fin 35) (Fin 35) (ZMod 461) :=
  ![inverseRow0, inverseRow1, inverseRow2, inverseRow3, inverseRow4, inverseRow5, inverseRow6, inverseRow7, inverseRow8, inverseRow9, inverseRow10, inverseRow11, inverseRow12, inverseRow13, inverseRow14, inverseRow15, inverseRow16, inverseRow17, inverseRow18, inverseRow19, inverseRow20, inverseRow21, inverseRow22, inverseRow23, inverseRow24, inverseRow25, inverseRow26, inverseRow27, inverseRow28, inverseRow29, inverseRow30, inverseRow31, inverseRow32, inverseRow33, inverseRow34]

def modularMatrix : Matrix (Fin 35) (Fin 35) (ZMod 461) :=
  (Int.castRingHom (ZMod 461)).mapMatrix integerMatrix

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_0 : ∀ j,
    (modularMatrix * modularInverse) 0 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 461)) 0 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_1 : ∀ j,
    (modularMatrix * modularInverse) 1 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 461)) 1 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_2 : ∀ j,
    (modularMatrix * modularInverse) 2 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 461)) 2 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_3 : ∀ j,
    (modularMatrix * modularInverse) 3 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 461)) 3 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_4 : ∀ j,
    (modularMatrix * modularInverse) 4 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 461)) 4 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_5 : ∀ j,
    (modularMatrix * modularInverse) 5 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 461)) 5 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_6 : ∀ j,
    (modularMatrix * modularInverse) 6 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 461)) 6 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_7 : ∀ j,
    (modularMatrix * modularInverse) 7 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 461)) 7 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_8 : ∀ j,
    (modularMatrix * modularInverse) 8 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 461)) 8 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_9 : ∀ j,
    (modularMatrix * modularInverse) 9 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 461)) 9 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_10 : ∀ j,
    (modularMatrix * modularInverse) 10 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 461)) 10 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_11 : ∀ j,
    (modularMatrix * modularInverse) 11 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 461)) 11 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_12 : ∀ j,
    (modularMatrix * modularInverse) 12 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 461)) 12 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_13 : ∀ j,
    (modularMatrix * modularInverse) 13 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 461)) 13 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_14 : ∀ j,
    (modularMatrix * modularInverse) 14 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 461)) 14 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_15 : ∀ j,
    (modularMatrix * modularInverse) 15 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 461)) 15 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_16 : ∀ j,
    (modularMatrix * modularInverse) 16 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 461)) 16 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_17 : ∀ j,
    (modularMatrix * modularInverse) 17 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 461)) 17 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_18 : ∀ j,
    (modularMatrix * modularInverse) 18 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 461)) 18 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_19 : ∀ j,
    (modularMatrix * modularInverse) 19 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 461)) 19 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_20 : ∀ j,
    (modularMatrix * modularInverse) 20 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 461)) 20 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_21 : ∀ j,
    (modularMatrix * modularInverse) 21 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 461)) 21 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_22 : ∀ j,
    (modularMatrix * modularInverse) 22 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 461)) 22 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_23 : ∀ j,
    (modularMatrix * modularInverse) 23 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 461)) 23 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_24 : ∀ j,
    (modularMatrix * modularInverse) 24 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 461)) 24 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_25 : ∀ j,
    (modularMatrix * modularInverse) 25 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 461)) 25 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_26 : ∀ j,
    (modularMatrix * modularInverse) 26 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 461)) 26 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_27 : ∀ j,
    (modularMatrix * modularInverse) 27 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 461)) 27 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_28 : ∀ j,
    (modularMatrix * modularInverse) 28 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 461)) 28 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_29 : ∀ j,
    (modularMatrix * modularInverse) 29 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 461)) 29 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_30 : ∀ j,
    (modularMatrix * modularInverse) 30 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 461)) 30 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_31 : ∀ j,
    (modularMatrix * modularInverse) 31 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 461)) 31 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_32 : ∀ j,
    (modularMatrix * modularInverse) 32 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 461)) 32 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_33 : ∀ j,
    (modularMatrix * modularInverse) 33 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 461)) 33 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_34 : ∀ j,
    (modularMatrix * modularInverse) 34 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 461)) 34 j := by
  decide

lemma inverse_certificate : modularMatrix * modularInverse = 1 := by
  ext i j
  fin_cases i
  · exact inverse_row_0 j
  · exact inverse_row_1 j
  · exact inverse_row_2 j
  · exact inverse_row_3 j
  · exact inverse_row_4 j
  · exact inverse_row_5 j
  · exact inverse_row_6 j
  · exact inverse_row_7 j
  · exact inverse_row_8 j
  · exact inverse_row_9 j
  · exact inverse_row_10 j
  · exact inverse_row_11 j
  · exact inverse_row_12 j
  · exact inverse_row_13 j
  · exact inverse_row_14 j
  · exact inverse_row_15 j
  · exact inverse_row_16 j
  · exact inverse_row_17 j
  · exact inverse_row_18 j
  · exact inverse_row_19 j
  · exact inverse_row_20 j
  · exact inverse_row_21 j
  · exact inverse_row_22 j
  · exact inverse_row_23 j
  · exact inverse_row_24 j
  · exact inverse_row_25 j
  · exact inverse_row_26 j
  · exact inverse_row_27 j
  · exact inverse_row_28 j
  · exact inverse_row_29 j
  · exact inverse_row_30 j
  · exact inverse_row_31 j
  · exact inverse_row_32 j
  · exact inverse_row_33 j
  · exact inverse_row_34 j

lemma modular_det_ne_zero : Matrix.det modularMatrix ≠ 0 := by
  intro h
  have hm := congrArg Matrix.det inverse_certificate
  rw [Matrix.det_mul, Matrix.det_one, h, zero_mul] at hm
  exact zero_ne_one hm

lemma integer_det_ne_zero : Matrix.det integerMatrix ≠ 0 := by
  intro h
  apply modular_det_ne_zero
  calc
    Matrix.det modularMatrix =
        (Int.castRingHom (ZMod 461)) (Matrix.det integerMatrix) :=
      ((Int.castRingHom (ZMod 461)).map_det integerMatrix).symm
    _ = 0 := by rw [h, map_zero]

def rationalMatrix : Matrix (Fin 35) (Fin 35) ℚ :=
  (Int.castRingHom ℚ).mapMatrix integerMatrix

lemma rational_det_ne_zero : Matrix.det rationalMatrix ≠ 0 := by
  intro h
  have hz : ((Matrix.det integerMatrix : ℤ) : ℚ) = 0 := by
    calc
      ((Matrix.det integerMatrix : ℤ) : ℚ) =
          Matrix.det rationalMatrix :=
        (Int.castRingHom ℚ).map_det integerMatrix
      _ = 0 := h
  exact integer_det_ne_zero (Int.cast_eq_zero.mp hz)

end PEqualNP.Outside.L_gct_231_aux.DiagonalAnchorMoment
