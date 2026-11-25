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

def reducedRow0 : Fin 35 → (ZMod 5) :=
  ![3, 1, 4, 2, 1, 1, 1, 0, 2, 0, 1, 0, 0, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def reducedRow1 : Fin 35 → (ZMod 5) :=
  ![0, 3, 0, 0, 0, 1, 4, 2, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 2, 0, 1, 0, 0, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def reducedRow2 : Fin 35 → (ZMod 5) :=
  ![0, 0, 3, 0, 0, 0, 1, 0, 0, 4, 2, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 2, 0, 0, 0, 0, 1, 0, 0, 4, 1, 0, 0, 0, 0]

def reducedRow3 : Fin 35 → (ZMod 5) :=
  ![0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 4, 0, 2, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 4, 1, 0]

def reducedRow4 : Fin 35 → (ZMod 5) :=
  ![0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 4, 0, 2, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 4, 1]

def reducedRow5 : Fin 35 → (ZMod 5) :=
  ![1, 1, 4, 0, 2, 1, 1, 4, 4, 3, 4, 0, 1, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def reducedRow6 : Fin 35 → (ZMod 5) :=
  ![0, 1, 0, 0, 0, 1, 4, 0, 2, 0, 0, 0, 0, 0, 0, 1, 1, 4, 4, 3, 4, 0, 1, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def reducedRow7 : Fin 35 → (ZMod 5) :=
  ![0, 0, 1, 0, 0, 0, 1, 0, 0, 4, 0, 2, 0, 0, 0, 0, 1, 0, 0, 1, 4, 4, 0, 0, 0, 3, 4, 0, 1, 0, 3, 0, 0, 0, 0]

def reducedRow8 : Fin 35 → (ZMod 5) :=
  ![0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 4, 0, 0, 2, 0, 0, 0, 1, 0, 0, 1, 0, 4, 4, 0, 0, 3, 0, 4, 0, 0, 1, 0, 3, 0]

def reducedRow9 : Fin 35 → (ZMod 5) :=
  ![0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 4, 0, 0, 2, 0, 0, 0, 1, 0, 0, 1, 0, 4, 4, 0, 0, 3, 0, 4, 0, 0, 1, 0, 3]

def reducedRow10 : Fin 35 → (ZMod 5) :=
  ![1, 3, 0, 3, 4, 0, 1, 3, 4, 0, 2, 2, 3, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def reducedRow11 : Fin 35 → (ZMod 5) :=
  ![0, 1, 0, 0, 0, 3, 0, 3, 4, 0, 0, 0, 0, 0, 0, 0, 1, 3, 4, 0, 2, 2, 3, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def reducedRow12 : Fin 35 → (ZMod 5) :=
  ![0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 3, 4, 0, 0, 0, 0, 0, 0, 0, 1, 3, 4, 0, 0, 0, 0, 2, 2, 3, 0, 4, 0, 0, 0, 0]

def reducedRow13 : Fin 35 → (ZMod 5) :=
  ![0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 0, 3, 4, 0, 0, 0, 0, 0, 0, 1, 0, 3, 4, 0, 0, 0, 0, 2, 2, 0, 3, 0, 4, 0]

def reducedRow14 : Fin 35 → (ZMod 5) :=
  ![0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 0, 3, 4, 0, 0, 0, 0, 0, 0, 1, 0, 3, 4, 0, 0, 0, 0, 2, 2, 0, 3, 0, 4]

def reducedRow15 : Fin 35 → (ZMod 5) :=
  ![4, 1, 1, 4, 4, 2, 3, 2, 1, 3, 1, 4, 3, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def reducedRow16 : Fin 35 → (ZMod 5) :=
  ![0, 4, 0, 0, 0, 1, 1, 4, 4, 0, 0, 0, 0, 0, 0, 2, 3, 2, 1, 3, 1, 4, 3, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def reducedRow17 : Fin 35 → (ZMod 5) :=
  ![0, 0, 4, 0, 0, 0, 1, 0, 0, 1, 4, 4, 0, 0, 0, 0, 2, 0, 0, 3, 2, 1, 0, 0, 0, 3, 1, 4, 3, 3, 1, 0, 0, 0, 0]

def reducedRow18 : Fin 35 → (ZMod 5) :=
  ![0, 0, 0, 4, 0, 0, 0, 1, 0, 0, 1, 0, 4, 4, 0, 0, 0, 2, 0, 0, 3, 0, 2, 1, 0, 0, 3, 0, 1, 4, 0, 3, 3, 1, 0]

def reducedRow19 : Fin 35 → (ZMod 5) :=
  ![0, 0, 0, 0, 4, 0, 0, 0, 1, 0, 0, 1, 0, 4, 4, 0, 0, 0, 2, 0, 0, 3, 0, 2, 1, 0, 0, 3, 0, 1, 4, 0, 3, 3, 1]

def reducedRow20 : Fin 35 → (ZMod 5) :=
  ![3, 0, 4, 1, 3, 2, 0, 4, 1, 3, 4, 2, 1, 4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def reducedRow21 : Fin 35 → (ZMod 5) :=
  ![0, 3, 0, 0, 0, 0, 4, 1, 3, 0, 0, 0, 0, 0, 0, 2, 0, 4, 1, 3, 4, 2, 1, 4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def reducedRow22 : Fin 35 → (ZMod 5) :=
  ![0, 0, 3, 0, 0, 0, 0, 0, 0, 4, 1, 3, 0, 0, 0, 0, 2, 0, 0, 0, 4, 1, 0, 0, 0, 3, 4, 2, 1, 4, 4, 0, 0, 0, 0]

def reducedRow23 : Fin 35 → (ZMod 5) :=
  ![0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 4, 0, 1, 3, 0, 0, 0, 2, 0, 0, 0, 0, 4, 1, 0, 0, 3, 0, 4, 2, 0, 1, 4, 4, 0]

def reducedRow24 : Fin 35 → (ZMod 5) :=
  ![0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 4, 0, 1, 3, 0, 0, 0, 2, 0, 0, 0, 0, 4, 1, 0, 0, 3, 0, 4, 2, 0, 1, 4, 4]

def reducedRow25 : Fin 35 → (ZMod 5) :=
  ![4, 2, 1, 0, 3, 2, 1, 4, 4, 0, 2, 1, 1, 4, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def reducedRow26 : Fin 35 → (ZMod 5) :=
  ![0, 4, 0, 0, 0, 2, 1, 0, 3, 0, 0, 0, 0, 0, 0, 2, 1, 4, 4, 0, 2, 1, 1, 4, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def reducedRow27 : Fin 35 → (ZMod 5) :=
  ![0, 0, 4, 0, 0, 0, 2, 0, 0, 1, 0, 3, 0, 0, 0, 0, 2, 0, 0, 1, 4, 4, 0, 0, 0, 0, 2, 1, 1, 4, 3, 0, 0, 0, 0]

def reducedRow28 : Fin 35 → (ZMod 5) :=
  ![0, 0, 0, 4, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3, 0, 0, 0, 2, 0, 0, 1, 0, 4, 4, 0, 0, 0, 0, 2, 1, 0, 1, 4, 3, 0]

def reducedRow29 : Fin 35 → (ZMod 5) :=
  ![0, 0, 0, 0, 4, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3, 0, 0, 0, 2, 0, 0, 1, 0, 4, 4, 0, 0, 0, 0, 2, 1, 0, 1, 4, 3]

def reducedRow30 : Fin 35 → (ZMod 5) :=
  ![1, 0, 0, 3, 4, 0, 2, 0, 3, 3, 1, 2, 1, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def reducedRow31 : Fin 35 → (ZMod 5) :=
  ![0, 1, 0, 0, 0, 0, 0, 3, 4, 0, 0, 0, 0, 0, 0, 0, 2, 0, 3, 3, 1, 2, 1, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def reducedRow32 : Fin 35 → (ZMod 5) :=
  ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 4, 0, 0, 0, 0, 0, 0, 0, 2, 0, 3, 0, 0, 0, 3, 1, 2, 1, 0, 4, 0, 0, 0, 0]

def reducedRow33 : Fin 35 → (ZMod 5) :=
  ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 3, 4, 0, 0, 0, 0, 0, 0, 2, 0, 0, 3, 0, 0, 3, 0, 1, 2, 0, 1, 0, 4, 0]

def reducedRow34 : Fin 35 → (ZMod 5) :=
  ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 3, 4, 0, 0, 0, 0, 0, 0, 2, 0, 0, 3, 0, 0, 3, 0, 1, 2, 0, 1, 0, 4]

def reducedMatrix : Matrix (Fin 35) (Fin 35) (ZMod 5) :=
  ![reducedRow0, reducedRow1, reducedRow2, reducedRow3, reducedRow4, reducedRow5, reducedRow6, reducedRow7, reducedRow8, reducedRow9, reducedRow10, reducedRow11, reducedRow12, reducedRow13, reducedRow14, reducedRow15, reducedRow16, reducedRow17, reducedRow18, reducedRow19, reducedRow20, reducedRow21, reducedRow22, reducedRow23, reducedRow24, reducedRow25, reducedRow26, reducedRow27, reducedRow28, reducedRow29, reducedRow30, reducedRow31, reducedRow32, reducedRow33, reducedRow34]

def inverseRow0 : Fin 35 → (ZMod 5) :=
  ![0, 4, 4, 2, 4, 0, 1, 2, 2, 1, 0, 4, 3, 0, 2, 0, 4, 3, 2, 3, 2, 1, 0, 1, 1, 0, 0, 2, 1, 1, 0, 4, 0, 0, 0]

def inverseRow1 : Fin 35 → (ZMod 5) :=
  ![4, 2, 1, 0, 4, 4, 2, 1, 1, 4, 2, 1, 4, 4, 0, 0, 1, 1, 3, 3, 4, 0, 0, 4, 2, 1, 2, 4, 2, 0, 1, 4, 3, 2, 2]

def inverseRow2 : Fin 35 → (ZMod 5) :=
  ![0, 0, 4, 1, 0, 0, 3, 2, 2, 4, 3, 0, 3, 3, 2, 1, 4, 1, 3, 1, 4, 0, 0, 3, 1, 2, 2, 1, 1, 3, 3, 4, 2, 1, 4]

def inverseRow3 : Fin 35 → (ZMod 5) :=
  ![2, 4, 1, 3, 1, 4, 3, 3, 1, 2, 4, 0, 2, 4, 2, 4, 2, 0, 1, 4, 3, 4, 3, 4, 0, 0, 3, 1, 1, 4, 1, 1, 4, 4, 1]

def inverseRow4 : Fin 35 → (ZMod 5) :=
  ![0, 1, 0, 0, 4, 4, 3, 4, 0, 1, 3, 3, 4, 0, 2, 2, 4, 4, 4, 3, 2, 1, 2, 3, 3, 0, 3, 1, 3, 0, 4, 0, 0, 2, 0]

def inverseRow5 : Fin 35 → (ZMod 5) :=
  ![4, 1, 2, 0, 1, 0, 3, 4, 4, 4, 2, 3, 0, 4, 1, 4, 4, 1, 1, 0, 4, 0, 0, 1, 1, 3, 4, 3, 1, 0, 1, 4, 0, 4, 1]

def inverseRow6 : Fin 35 → (ZMod 5) :=
  ![0, 0, 1, 2, 0, 4, 4, 1, 4, 2, 4, 0, 3, 3, 4, 2, 3, 0, 3, 3, 2, 1, 1, 0, 0, 4, 4, 3, 3, 2, 2, 4, 3, 0, 1]

def inverseRow7 : Fin 35 → (ZMod 5) :=
  ![3, 0, 0, 2, 4, 1, 4, 1, 3, 4, 1, 0, 0, 4, 3, 2, 3, 1, 0, 0, 0, 3, 0, 4, 3, 3, 2, 4, 0, 0, 4, 2, 3, 1, 0]

def inverseRow8 : Fin 35 → (ZMod 5) :=
  ![1, 0, 2, 4, 4, 0, 4, 3, 3, 1, 3, 0, 1, 2, 3, 3, 1, 4, 1, 4, 1, 3, 1, 2, 0, 4, 4, 1, 3, 4, 3, 1, 2, 3, 0]

def inverseRow9 : Fin 35 → (ZMod 5) :=
  ![2, 3, 4, 3, 1, 0, 1, 0, 2, 2, 2, 2, 0, 3, 1, 4, 4, 3, 2, 2, 4, 2, 4, 1, 4, 2, 2, 4, 0, 1, 1, 2, 3, 2, 2]

def inverseRow10 : Fin 35 → (ZMod 5) :=
  ![0, 1, 3, 0, 0, 1, 1, 2, 3, 3, 3, 0, 2, 1, 2, 1, 2, 3, 3, 0, 3, 1, 1, 1, 2, 0, 1, 4, 4, 0, 3, 0, 4, 0, 0]

def inverseRow11 : Fin 35 → (ZMod 5) :=
  ![2, 4, 4, 4, 4, 0, 2, 2, 2, 2, 3, 3, 4, 3, 1, 4, 1, 1, 0, 4, 1, 4, 3, 3, 3, 4, 2, 0, 0, 3, 1, 1, 4, 1, 4]

def inverseRow12 : Fin 35 → (ZMod 5) :=
  ![2, 1, 0, 3, 0, 4, 2, 0, 1, 0, 3, 4, 4, 0, 4, 2, 0, 3, 3, 3, 4, 2, 3, 3, 0, 2, 4, 3, 0, 3, 4, 3, 4, 2, 3]

def inverseRow13 : Fin 35 → (ZMod 5) :=
  ![4, 4, 4, 3, 2, 2, 4, 2, 0, 0, 4, 1, 3, 1, 2, 3, 4, 3, 3, 0, 2, 0, 1, 0, 3, 0, 2, 1, 3, 4, 4, 3, 4, 0, 4]

def inverseRow14 : Fin 35 → (ZMod 5) :=
  ![1, 4, 3, 2, 1, 1, 2, 4, 1, 1, 4, 2, 3, 0, 4, 1, 1, 3, 2, 2, 2, 0, 4, 4, 3, 1, 1, 2, 0, 1, 3, 4, 4, 4, 2]

def inverseRow15 : Fin 35 → (ZMod 5) :=
  ![0, 1, 3, 1, 2, 2, 4, 3, 0, 0, 1, 0, 4, 3, 3, 4, 4, 0, 4, 4, 3, 4, 1, 3, 1, 0, 0, 4, 0, 2, 2, 1, 1, 1, 3]

def inverseRow16 : Fin 35 → (ZMod 5) :=
  ![3, 4, 0, 0, 1, 2, 1, 1, 1, 4, 2, 4, 4, 0, 4, 1, 3, 1, 4, 1, 3, 1, 0, 4, 0, 0, 1, 0, 4, 3, 4, 2, 3, 4, 4]

def inverseRow17 : Fin 35 → (ZMod 5) :=
  ![1, 1, 3, 2, 4, 4, 2, 1, 2, 0, 3, 0, 3, 2, 3, 0, 1, 4, 3, 0, 4, 1, 2, 3, 3, 0, 4, 4, 0, 4, 3, 3, 3, 0, 0]

def inverseRow18 : Fin 35 → (ZMod 5) :=
  ![2, 2, 3, 2, 0, 0, 0, 1, 4, 0, 3, 3, 1, 2, 3, 4, 2, 2, 3, 0, 0, 1, 2, 2, 3, 0, 1, 2, 4, 2, 0, 1, 0, 0, 0]

def inverseRow19 : Fin 35 → (ZMod 5) :=
  ![3, 0, 0, 2, 4, 1, 0, 3, 3, 2, 0, 3, 2, 4, 3, 1, 1, 0, 3, 0, 3, 2, 3, 4, 4, 2, 2, 4, 2, 4, 4, 0, 4, 0, 0]

def inverseRow20 : Fin 35 → (ZMod 5) :=
  ![3, 4, 4, 1, 2, 3, 3, 1, 1, 1, 1, 2, 0, 2, 1, 4, 3, 0, 2, 2, 1, 3, 4, 3, 3, 1, 3, 3, 0, 3, 4, 0, 0, 4, 2]

def inverseRow21 : Fin 35 → (ZMod 5) :=
  ![2, 0, 4, 3, 2, 4, 1, 1, 3, 4, 4, 1, 2, 0, 0, 2, 4, 3, 1, 2, 1, 4, 4, 3, 0, 1, 4, 2, 2, 1, 1, 2, 2, 4, 4]

def inverseRow22 : Fin 35 → (ZMod 5) :=
  ![1, 1, 4, 1, 3, 0, 4, 4, 1, 1, 4, 0, 0, 0, 1, 2, 3, 2, 3, 2, 1, 0, 1, 2, 2, 3, 2, 3, 4, 4, 0, 2, 3, 4, 2]

def inverseRow23 : Fin 35 → (ZMod 5) :=
  ![4, 0, 3, 4, 0, 2, 1, 0, 0, 2, 2, 4, 4, 1, 4, 1, 3, 1, 4, 1, 4, 1, 1, 3, 0, 1, 3, 0, 2, 3, 4, 3, 3, 0, 2]

def inverseRow24 : Fin 35 → (ZMod 5) :=
  ![1, 1, 4, 2, 0, 0, 1, 2, 3, 4, 3, 1, 4, 4, 4, 0, 3, 1, 0, 4, 2, 3, 2, 1, 2, 3, 3, 3, 3, 4, 1, 1, 0, 1, 2]

def inverseRow25 : Fin 35 → (ZMod 5) :=
  ![3, 1, 2, 0, 4, 4, 1, 0, 4, 3, 4, 0, 0, 1, 0, 0, 1, 2, 4, 1, 0, 1, 0, 3, 4, 3, 2, 0, 2, 2, 1, 1, 0, 1, 1]

def inverseRow26 : Fin 35 → (ZMod 5) :=
  ![4, 0, 2, 2, 4, 4, 0, 4, 4, 3, 3, 0, 1, 0, 2, 3, 1, 0, 0, 0, 3, 4, 4, 3, 4, 2, 0, 4, 0, 0, 2, 0, 2, 3, 2]

def inverseRow27 : Fin 35 → (ZMod 5) :=
  ![4, 4, 3, 4, 3, 0, 3, 0, 3, 3, 0, 2, 3, 0, 2, 1, 3, 3, 3, 0, 3, 2, 0, 2, 3, 2, 4, 2, 0, 2, 2, 0, 2, 1, 3]

def inverseRow28 : Fin 35 → (ZMod 5) :=
  ![1, 3, 0, 4, 2, 2, 3, 1, 4, 0, 0, 3, 3, 1, 3, 4, 3, 4, 2, 3, 0, 0, 0, 4, 4, 4, 4, 0, 1, 2, 3, 2, 0, 2, 4]

def inverseRow29 : Fin 35 → (ZMod 5) :=
  ![1, 0, 3, 0, 0, 1, 3, 3, 0, 2, 4, 3, 1, 3, 0, 3, 0, 3, 1, 2, 3, 1, 4, 0, 2, 2, 0, 2, 4, 0, 3, 0, 0, 4, 1]

def inverseRow30 : Fin 35 → (ZMod 5) :=
  ![2, 3, 0, 4, 4, 0, 4, 0, 0, 0, 1, 3, 0, 0, 2, 2, 1, 4, 1, 4, 0, 1, 2, 0, 3, 4, 2, 0, 0, 3, 4, 4, 4, 2, 2]

def inverseRow31 : Fin 35 → (ZMod 5) :=
  ![4, 4, 0, 0, 3, 4, 0, 1, 1, 4, 4, 0, 3, 2, 4, 3, 1, 3, 1, 1, 4, 0, 1, 1, 3, 2, 2, 2, 0, 3, 3, 4, 0, 0, 3]

def inverseRow32 : Fin 35 → (ZMod 5) :=
  ![1, 3, 3, 2, 2, 1, 3, 1, 0, 4, 1, 3, 3, 2, 1, 0, 4, 4, 2, 3, 0, 2, 1, 4, 0, 1, 1, 0, 0, 1, 1, 2, 4, 4, 4]

def inverseRow33 : Fin 35 → (ZMod 5) :=
  ![1, 3, 1, 3, 0, 1, 3, 3, 3, 2, 3, 1, 4, 4, 4, 0, 0, 2, 3, 3, 1, 3, 3, 2, 1, 2, 4, 3, 3, 4, 2, 2, 2, 1, 1]

def inverseRow34 : Fin 35 → (ZMod 5) :=
  ![1, 3, 4, 1, 2, 4, 1, 3, 3, 0, 0, 2, 4, 0, 2, 4, 2, 3, 2, 0, 1, 4, 4, 3, 2, 2, 2, 3, 4, 3, 1, 2, 0, 4, 1]

def modularInverse : Matrix (Fin 35) (Fin 35) (ZMod 5) :=
  ![inverseRow0, inverseRow1, inverseRow2, inverseRow3, inverseRow4, inverseRow5, inverseRow6, inverseRow7, inverseRow8, inverseRow9, inverseRow10, inverseRow11, inverseRow12, inverseRow13, inverseRow14, inverseRow15, inverseRow16, inverseRow17, inverseRow18, inverseRow19, inverseRow20, inverseRow21, inverseRow22, inverseRow23, inverseRow24, inverseRow25, inverseRow26, inverseRow27, inverseRow28, inverseRow29, inverseRow30, inverseRow31, inverseRow32, inverseRow33, inverseRow34]

def modularMatrix : Matrix (Fin 35) (Fin 35) (ZMod 5) :=
  (Int.castRingHom (ZMod 5)).mapMatrix integerMatrix

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma reduced_row_0 : ∀ j,
    modularMatrix 0 j = reducedMatrix 0 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma reduced_row_1 : ∀ j,
    modularMatrix 1 j = reducedMatrix 1 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma reduced_row_2 : ∀ j,
    modularMatrix 2 j = reducedMatrix 2 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma reduced_row_3 : ∀ j,
    modularMatrix 3 j = reducedMatrix 3 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma reduced_row_4 : ∀ j,
    modularMatrix 4 j = reducedMatrix 4 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma reduced_row_5 : ∀ j,
    modularMatrix 5 j = reducedMatrix 5 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma reduced_row_6 : ∀ j,
    modularMatrix 6 j = reducedMatrix 6 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma reduced_row_7 : ∀ j,
    modularMatrix 7 j = reducedMatrix 7 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma reduced_row_8 : ∀ j,
    modularMatrix 8 j = reducedMatrix 8 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma reduced_row_9 : ∀ j,
    modularMatrix 9 j = reducedMatrix 9 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma reduced_row_10 : ∀ j,
    modularMatrix 10 j = reducedMatrix 10 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma reduced_row_11 : ∀ j,
    modularMatrix 11 j = reducedMatrix 11 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma reduced_row_12 : ∀ j,
    modularMatrix 12 j = reducedMatrix 12 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma reduced_row_13 : ∀ j,
    modularMatrix 13 j = reducedMatrix 13 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma reduced_row_14 : ∀ j,
    modularMatrix 14 j = reducedMatrix 14 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma reduced_row_15 : ∀ j,
    modularMatrix 15 j = reducedMatrix 15 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma reduced_row_16 : ∀ j,
    modularMatrix 16 j = reducedMatrix 16 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma reduced_row_17 : ∀ j,
    modularMatrix 17 j = reducedMatrix 17 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma reduced_row_18 : ∀ j,
    modularMatrix 18 j = reducedMatrix 18 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma reduced_row_19 : ∀ j,
    modularMatrix 19 j = reducedMatrix 19 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma reduced_row_20 : ∀ j,
    modularMatrix 20 j = reducedMatrix 20 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma reduced_row_21 : ∀ j,
    modularMatrix 21 j = reducedMatrix 21 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma reduced_row_22 : ∀ j,
    modularMatrix 22 j = reducedMatrix 22 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma reduced_row_23 : ∀ j,
    modularMatrix 23 j = reducedMatrix 23 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma reduced_row_24 : ∀ j,
    modularMatrix 24 j = reducedMatrix 24 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma reduced_row_25 : ∀ j,
    modularMatrix 25 j = reducedMatrix 25 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma reduced_row_26 : ∀ j,
    modularMatrix 26 j = reducedMatrix 26 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma reduced_row_27 : ∀ j,
    modularMatrix 27 j = reducedMatrix 27 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma reduced_row_28 : ∀ j,
    modularMatrix 28 j = reducedMatrix 28 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma reduced_row_29 : ∀ j,
    modularMatrix 29 j = reducedMatrix 29 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma reduced_row_30 : ∀ j,
    modularMatrix 30 j = reducedMatrix 30 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma reduced_row_31 : ∀ j,
    modularMatrix 31 j = reducedMatrix 31 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma reduced_row_32 : ∀ j,
    modularMatrix 32 j = reducedMatrix 32 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma reduced_row_33 : ∀ j,
    modularMatrix 33 j = reducedMatrix 33 j := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma reduced_row_34 : ∀ j,
    modularMatrix 34 j = reducedMatrix 34 j := by
  decide

lemma reduced_matrix : modularMatrix = reducedMatrix := by
  ext i j
  fin_cases i
  · exact reduced_row_0 j
  · exact reduced_row_1 j
  · exact reduced_row_2 j
  · exact reduced_row_3 j
  · exact reduced_row_4 j
  · exact reduced_row_5 j
  · exact reduced_row_6 j
  · exact reduced_row_7 j
  · exact reduced_row_8 j
  · exact reduced_row_9 j
  · exact reduced_row_10 j
  · exact reduced_row_11 j
  · exact reduced_row_12 j
  · exact reduced_row_13 j
  · exact reduced_row_14 j
  · exact reduced_row_15 j
  · exact reduced_row_16 j
  · exact reduced_row_17 j
  · exact reduced_row_18 j
  · exact reduced_row_19 j
  · exact reduced_row_20 j
  · exact reduced_row_21 j
  · exact reduced_row_22 j
  · exact reduced_row_23 j
  · exact reduced_row_24 j
  · exact reduced_row_25 j
  · exact reduced_row_26 j
  · exact reduced_row_27 j
  · exact reduced_row_28 j
  · exact reduced_row_29 j
  · exact reduced_row_30 j
  · exact reduced_row_31 j
  · exact reduced_row_32 j
  · exact reduced_row_33 j
  · exact reduced_row_34 j

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_0 : ∀ j,
    (reducedMatrix * modularInverse) 0 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 5)) 0 j := by
  decide

#check inverse_row_0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_1 : ∀ j,
    (reducedMatrix * modularInverse) 1 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 5)) 1 j := by
  decide

#check inverse_row_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_2 : ∀ j,
    (reducedMatrix * modularInverse) 2 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 5)) 2 j := by
  decide

#check inverse_row_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_3 : ∀ j,
    (reducedMatrix * modularInverse) 3 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 5)) 3 j := by
  decide

#check inverse_row_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_4 : ∀ j,
    (reducedMatrix * modularInverse) 4 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 5)) 4 j := by
  decide

#check inverse_row_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_5 : ∀ j,
    (reducedMatrix * modularInverse) 5 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 5)) 5 j := by
  decide

#check inverse_row_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_6 : ∀ j,
    (reducedMatrix * modularInverse) 6 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 5)) 6 j := by
  decide

#check inverse_row_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_7 : ∀ j,
    (reducedMatrix * modularInverse) 7 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 5)) 7 j := by
  decide

#check inverse_row_7

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_8 : ∀ j,
    (reducedMatrix * modularInverse) 8 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 5)) 8 j := by
  decide

#check inverse_row_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_9 : ∀ j,
    (reducedMatrix * modularInverse) 9 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 5)) 9 j := by
  decide

#check inverse_row_9

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_10 : ∀ j,
    (reducedMatrix * modularInverse) 10 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 5)) 10 j := by
  decide

#check inverse_row_10

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_11 : ∀ j,
    (reducedMatrix * modularInverse) 11 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 5)) 11 j := by
  decide

#check inverse_row_11

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_12 : ∀ j,
    (reducedMatrix * modularInverse) 12 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 5)) 12 j := by
  decide

#check inverse_row_12

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_13 : ∀ j,
    (reducedMatrix * modularInverse) 13 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 5)) 13 j := by
  decide

#check inverse_row_13

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_14 : ∀ j,
    (reducedMatrix * modularInverse) 14 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 5)) 14 j := by
  decide

#check inverse_row_14

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_15 : ∀ j,
    (reducedMatrix * modularInverse) 15 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 5)) 15 j := by
  decide

#check inverse_row_15

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_16 : ∀ j,
    (reducedMatrix * modularInverse) 16 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 5)) 16 j := by
  decide

#check inverse_row_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_17 : ∀ j,
    (reducedMatrix * modularInverse) 17 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 5)) 17 j := by
  decide

#check inverse_row_17

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_18 : ∀ j,
    (reducedMatrix * modularInverse) 18 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 5)) 18 j := by
  decide

#check inverse_row_18

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_19 : ∀ j,
    (reducedMatrix * modularInverse) 19 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 5)) 19 j := by
  decide

#check inverse_row_19

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_20 : ∀ j,
    (reducedMatrix * modularInverse) 20 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 5)) 20 j := by
  decide

#check inverse_row_20

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_21 : ∀ j,
    (reducedMatrix * modularInverse) 21 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 5)) 21 j := by
  decide

#check inverse_row_21

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_22 : ∀ j,
    (reducedMatrix * modularInverse) 22 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 5)) 22 j := by
  decide

#check inverse_row_22

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_23 : ∀ j,
    (reducedMatrix * modularInverse) 23 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 5)) 23 j := by
  decide

#check inverse_row_23

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_24 : ∀ j,
    (reducedMatrix * modularInverse) 24 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 5)) 24 j := by
  decide

#check inverse_row_24

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_25 : ∀ j,
    (reducedMatrix * modularInverse) 25 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 5)) 25 j := by
  decide

#check inverse_row_25

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_26 : ∀ j,
    (reducedMatrix * modularInverse) 26 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 5)) 26 j := by
  decide

#check inverse_row_26

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_27 : ∀ j,
    (reducedMatrix * modularInverse) 27 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 5)) 27 j := by
  decide

#check inverse_row_27

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_28 : ∀ j,
    (reducedMatrix * modularInverse) 28 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 5)) 28 j := by
  decide

#check inverse_row_28

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_29 : ∀ j,
    (reducedMatrix * modularInverse) 29 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 5)) 29 j := by
  decide

#check inverse_row_29

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_30 : ∀ j,
    (reducedMatrix * modularInverse) 30 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 5)) 30 j := by
  decide

#check inverse_row_30

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_31 : ∀ j,
    (reducedMatrix * modularInverse) 31 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 5)) 31 j := by
  decide

#check inverse_row_31

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_32 : ∀ j,
    (reducedMatrix * modularInverse) 32 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 5)) 32 j := by
  decide

#check inverse_row_32

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_33 : ∀ j,
    (reducedMatrix * modularInverse) 33 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 5)) 33 j := by
  decide

#check inverse_row_33

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma inverse_row_34 : ∀ j,
    (reducedMatrix * modularInverse) 34 j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 5)) 34 j := by
  decide

#check inverse_row_34

lemma inverse_certificate : modularMatrix * modularInverse = 1 := by
  rw [reduced_matrix]
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
        (Int.castRingHom (ZMod 5)) (Matrix.det integerMatrix) :=
      ((Int.castRingHom (ZMod 5)).map_det integerMatrix).symm
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
