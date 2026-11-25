import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.GroupTheory.Perm.Fin

namespace PEqualNP.Outside.L_gct_231_aux.TopAllZeroBridge

noncomputable def ca (x y : ℂ) : ℂ := x+y
noncomputable def cm (x y : ℂ) : ℂ := x*y
noncomputable def cp (x : ℂ) (n : ℕ) : ℂ := x^n
noncomputable def cz (z : ℤ) : ℂ := z

noncomputable def p0 (a b c l m n h : ℂ) : ℂ :=
  ca (cm ((cz (1))) (cp h 2)) ((cz (-24)))

noncomputable def p1 (a b c l m n h : ℂ) : ℂ :=
  ca (cm (ca (cm (cm ((cz (2))) (cp c 2)) a) (ca (cm (cm ((cz (4))) (cp c 2)) b) (cm (ca (cm ((cz (-4))) (cp c 2)) (ca (cm ((cz (4))) m) (ca (cm ((cz (4))) n) (cm ((cz (4))) h)))) c))) a) (ca (cm (ca (cm (cm ((cz (2))) (cp c 2)) b) (cm (ca (cm ((cz (-4))) (cp c 2)) (ca (cm ((cz (4))) m) (ca (cm ((cz (4))) n) (cm ((cz (4))) h)))) c)) b) (ca (cm (ca (cm (ca (cm ((cz (-6))) c) ((cz (64)))) c) (ca (cm ((cz (-4))) m) (ca (cm ((cz (-4))) n) ((cz (-144)))))) (cp c 2)) (ca (cm (ca (cm ((cz (2))) m) (ca (cm ((cz (4))) n) (cm ((cz (4))) h))) m) (ca (cm (ca (cm ((cz (2))) n) (cm ((cz (4))) h)) n) ((cz (48)))))))

noncomputable def p2 (a b c l m n h : ℂ) : ℂ :=
  ca (cm (ca (cm (cm (cm ((cz (12))) c) b) a) (ca (cm (ca (cm (cm ((cz (16))) c) b) (ca (cm (ca (cm ((cz (16))) c) ((cz (-128)))) c) (ca (cm ((cz (12))) m) (ca (cm ((cz (4))) n) (cm ((cz (4))) h))))) b) (cm (ca (cm ((cz (12))) l) (ca (cm ((cz (-4))) n) (cm ((cz (4))) h))) c))) a) (ca (cm (ca (cm (ca (cm (cm ((cz (4))) c) b) (ca (cm (ca (cm ((cz (8))) c) ((cz (-64)))) c) (ca (cm ((cz (12))) m) (ca (cm ((cz (4))) n) (cm ((cz (4))) h))))) b) (ca (cm (ca (cm (ca (cm ((cz (4))) c) ((cz (-64)))) c) (ca (cm ((cz (4))) l) (ca (cm ((cz (4))) m) ((cz (224)))))) c) (cm ((cz (-64))) m))) b) (ca (cm (ca (cm (ca (cm ((cz (12))) l) (ca (cm ((cz (-4))) n) (cm ((cz (4))) h))) c) (cm ((cz (-64))) l)) c) (ca (cm (ca (cm ((cz (12))) m) (ca (cm ((cz (4))) n) (cm ((cz (4))) h))) l) (ca (cm (ca (cm ((cz (-4))) n) (cm ((cz (4))) h)) m) (ca (cm ((cz (4))) (cp n 2)) (ca (cm ((cz (-8))) (cp h 2)) ((cz (96)))))))))

noncomputable def p3 (a b c l m n h : ℂ) : ℂ :=
  ca (cm (ca (cm (cm ((cz (2))) (cp b 2)) a) (cm (ca (cm (ca (cm ((cz (-4))) b) (cm ((cz (4))) c)) b) (ca (cm ((cz (4))) l) (ca (cm ((cz (-4))) n) (cm ((cz (4))) h)))) b)) a) (ca (cm (ca (cm (ca (cm (ca (cm ((cz (-6))) b) (ca (cm ((cz (-4))) c) ((cz (64))))) b) (ca (cm ((cz (2))) (cp c 2)) (ca (cm ((cz (-4))) l) (ca (cm ((cz (4))) n) ((cz (-144))))))) b) (cm (ca (cm ((cz (4))) l) (ca (cm ((cz (-4))) n) (cm ((cz (4))) h))) c)) b) (ca (cm (ca (cm ((cz (2))) l) (ca (cm ((cz (-4))) n) (cm ((cz (4))) h))) l) (ca (cm (ca (cm ((cz (2))) n) (cm ((cz (-4))) h)) n) ((cz (48))))))

noncomputable def p4 (a b c l m n h : ℂ) : ℂ :=
  ca (cm (ca (cm (ca (cm (cm ((cz (4))) c) a) (ca (cm (cm ((cz (16))) c) b) (ca (cm (ca (cm ((cz (8))) c) ((cz (-64)))) c) (ca (cm ((cz (4))) m) (ca (cm ((cz (12))) n) (cm ((cz (4))) h)))))) a) (ca (cm (ca (cm (cm ((cz (12))) c) b) (ca (cm (ca (cm ((cz (16))) c) ((cz (-128)))) c) (ca (cm ((cz (4))) m) (ca (cm ((cz (12))) n) (cm ((cz (4))) h))))) b) (ca (cm (ca (cm (ca (cm ((cz (4))) c) ((cz (-64)))) c) (ca (cm ((cz (-4))) l) (ca (cm ((cz (4))) n) ((cz (224)))))) c) (cm ((cz (-64))) n)))) a) (ca (cm (cm (ca (cm ((cz (-12))) l) (ca (cm ((cz (-4))) m) (cm ((cz (4))) h))) c) b) (ca (cm (ca (cm (ca (cm ((cz (-12))) l) (ca (cm ((cz (-4))) m) (cm ((cz (4))) h))) c) (cm ((cz (64))) l)) c) (ca (cm (ca (cm ((cz (-4))) m) (ca (cm ((cz (-12))) n) (cm ((cz (-4))) h))) l) (ca (cm (ca (cm ((cz (4))) m) (cm ((cz (-4))) n)) m) (ca (cm (cm ((cz (4))) h) n) (ca (cm ((cz (-8))) (cp h 2)) ((cz (96)))))))))

noncomputable def p5 (a b c l m n h : ℂ) : ℂ :=
  ca (cm (ca (cm (ca (cm (cm ((cz (4))) b) a) (ca (cm (ca (cm ((cz (8))) b) (ca (cm ((cz (16))) c) ((cz (-64))))) b) (ca (cm ((cz (4))) l) (ca (cm ((cz (-12))) n) (cm ((cz (4))) h))))) a) (ca (cm (ca (cm (ca (cm ((cz (4))) b) (ca (cm ((cz (16))) c) ((cz (-64))))) b) (ca (cm (ca (cm ((cz (12))) c) ((cz (-128)))) c) (ca (cm ((cz (-4))) m) (ca (cm ((cz (-4))) n) ((cz (224))))))) b) (ca (cm (ca (cm ((cz (4))) l) (ca (cm ((cz (-12))) n) (cm ((cz (4))) h))) c) (cm ((cz (64))) n)))) a) (ca (cm (ca (cm (ca (cm ((cz (-4))) l) (ca (cm ((cz (-12))) m) (cm ((cz (4))) h))) b) (ca (cm (ca (cm ((cz (-4))) l) (ca (cm ((cz (-12))) m) (cm ((cz (4))) h))) c) (cm ((cz (64))) m))) b) (ca (cm (ca (cm ((cz (4))) l) (ca (cm ((cz (-4))) m) (cm ((cz (4))) n))) l) (ca (cm (ca (cm ((cz (12))) n) (cm ((cz (-4))) h)) m) (ca (cm (cm ((cz (-4))) h) n) (ca (cm ((cz (-8))) (cp h 2)) ((cz (96))))))))

noncomputable def p6 (a b c l m n h : ℂ) : ℂ :=
  ca (cm (ca (cm (ca (cm (ca (cm ((cz (-6))) a) (ca (cm ((cz (-4))) b) (ca (cm ((cz (-4))) c) ((cz (64)))))) a) (ca (cm (ca (cm ((cz (2))) b) (cm ((cz (4))) c)) b) (ca (cm ((cz (2))) (cp c 2)) (ca (cm ((cz (4))) l) (ca (cm ((cz (4))) m) ((cz (-144)))))))) a) (ca (cm (ca (cm ((cz (-4))) l) (ca (cm ((cz (-4))) m) (cm ((cz (4))) h))) b) (cm (ca (cm ((cz (-4))) l) (ca (cm ((cz (-4))) m) (cm ((cz (4))) h))) c))) a) (ca (cm (ca (cm ((cz (2))) l) (ca (cm ((cz (4))) m) (cm ((cz (-4))) h))) l) (ca (cm (ca (cm ((cz (2))) m) (cm ((cz (-4))) h)) m) ((cz (48)))))

noncomputable def p7 (a b c l m n h : ℂ) : ℂ :=
  ca (cm (ca (cm (cm ((cz (2))) (cp c 4)) b) (cm (ca (cm ((cz (-2))) (cp c 2)) (ca (cm ((cz (2))) n) (cm ((cz (2))) h))) (cp c 3))) a) (ca (cm (cm (ca (cm ((cz (-2))) (cp c 2)) (ca (cm ((cz (2))) m) (cm ((cz (2))) h))) (cp c 3)) b) (cm (ca (cm (ca (cm (ca (cm (ca (cm ((cz (-2))) c) ((cz (16)))) c) (ca (cm ((cz (-2))) m) (cm ((cz (-2))) n))) c) ((cz (-96)))) c) (ca (cm (ca (cm ((cz (2))) n) (cm ((cz (2))) h)) m) (ca (cm (cm ((cz (2))) h) n) ((cz (48)))))) (cp c 2)))

noncomputable def p8 (a b c l m n h : ℂ) : ℂ :=
  ca (cm (ca (cm (ca (cm (ca (cm (cm ((cz (-2))) (cp c 2)) b) (cm (ca (cm ((cz (6))) (cp c 2)) (ca (cm ((cz (-4))) n) (cm ((cz (-4))) h))) c)) b) (ca (cm (ca (cm ((cz (-4))) (cp c 2)) (ca (cm ((cz (2))) n) (cm ((cz (6))) h))) (cp c 2)) (ca (cm (ca (cm ((cz (-2))) n) (cm ((cz (-4))) h)) n) ((cz (-48)))))) b) (cm (ca (cm (ca (cm ((cz (4))) n) (cm ((cz (-4))) h)) (cp c 2)) (ca (cm ((cz (-2))) (cp n 2)) ((cz (48))))) c)) a) (ca (cm (ca (cm (ca (cm (ca (cm (cm ((cz (-2))) (cp c 2)) b) (cm (ca (cm (ca (cm ((cz (-2))) c) ((cz (16)))) c) (ca (cm ((cz (-4))) n) (cm ((cz (-4))) h))) c)) b) (ca (cm (ca (cm (ca (cm ((cz (-4))) (cp c 2)) (ca (cm ((cz (-2))) l) (ca (cm ((cz (4))) m) (cm ((cz (-2))) n)))) c) (ca (cm ((cz (32))) n) (cm ((cz (32))) h))) c) (ca (cm (ca (cm ((cz (-2))) n) (cm ((cz (-4))) h)) n) ((cz (-48)))))) b) (ca (cm (ca (cm (ca (cm (ca (cm (ca (cm ((cz (-4))) c) ((cz (32)))) c) (ca (cm ((cz (2))) l) (ca (cm ((cz (-4))) m) (cm ((cz (-2))) h)))) c) ((cz (-288)))) c) (ca (cm (ca (cm ((cz (-4))) n) (cm ((cz (-4))) h)) l) (ca (cm (cm ((cz (4))) h) m) (ca (cm ((cz (2))) (cp n 2)) (ca (cm ((cz (-4))) (cp h 2)) ((cz (48)))))))) c) (ca (cm (ca (cm ((cz (16))) n) (cm ((cz (32))) h)) n) ((cz (384)))))) b) (ca (cm (ca (cm (ca (cm (ca (cm ((cz (4))) n) (cm ((cz (-4))) h)) c) (ca (cm ((cz (-32))) n) (cm ((cz (32))) h))) c) (ca (cm (ca (cm ((cz (2))) n) (cm ((cz (2))) h)) l) (ca (cm (ca (cm ((cz (4))) n) (cm ((cz (-4))) h)) m) (ca (cm (ca (cm ((cz (4))) n) (cm ((cz (-2))) h)) n) (ca (cm ((cz (-4))) (cp h 2)) ((cz (48)))))))) (cp c 2)) (ca (cm (ca (cm (ca (cm ((cz (-2))) n) (cm ((cz (-4))) h)) n) ((cz (-48)))) l) (ca (cm (ca (cm ((cz (-2))) (cp n 2)) ((cz (48)))) m) (ca (cm (ca (cm (ca (cm ((cz (2))) n) (cm ((cz (2))) h)) n) (ca (cm ((cz (-4))) (cp h 2)) ((cz (48))))) n) (cm ((cz (-48))) h))))))

noncomputable def p9 (a b c l m n h : ℂ) : ℂ :=
  ca (cm (ca (cm (ca (cm (ca (cm (ca (cm (cm ((cz (-4))) c) b) (ca (cm ((cz (6))) (cp c 2)) (ca (cm ((cz (-4))) n) (cm ((cz (-4))) h)))) b) (cm (ca (cm ((cz (-2))) (cp c 2)) (ca (cm ((cz (-2))) n) (cm ((cz (6))) h))) c)) b) (ca (cm (ca (cm ((cz (4))) n) (cm ((cz (-4))) h)) (cp c 2)) (ca (cm ((cz (-2))) (cp n 2)) ((cz (48)))))) b) (cm (ca (cm (ca (cm ((cz (-2))) n) (cm ((cz (4))) h)) n) ((cz (-48)))) c)) a) (ca (cm (ca (cm (ca (cm (ca (cm (ca (cm (cm ((cz (-4))) c) b) (ca (cm (ca (cm ((cz (-4))) c) ((cz (32)))) c) (ca (cm ((cz (-4))) n) (cm ((cz (-4))) h)))) b) (ca (cm (ca (cm ((cz (-2))) (cp c 2)) (ca (cm ((cz (-4))) l) (ca (cm ((cz (2))) m) (cm ((cz (-2))) h)))) c) (ca (cm ((cz (32))) n) (cm ((cz (32))) h)))) b) (ca (cm (ca (cm (ca (cm (ca (cm ((cz (-2))) c) ((cz (16)))) c) (ca (cm ((cz (4))) l) (ca (cm ((cz (-2))) m) (cm ((cz (2))) n)))) c) ((cz (-288)))) c) (ca (cm (ca (cm ((cz (-4))) n) (cm ((cz (-4))) h)) l) (ca (cm (ca (cm ((cz (-2))) n) (cm ((cz (2))) h)) m) (ca (cm (ca (cm ((cz (4))) n) (cm ((cz (2))) h)) n) (ca (cm ((cz (-4))) (cp h 2)) ((cz (48))))))))) b) (cm (ca (cm (ca (cm (ca (cm ((cz (4))) n) (cm ((cz (-4))) h)) c) (ca (cm ((cz (-32))) n) (cm ((cz (32))) h))) c) (ca (cm (cm ((cz (4))) h) l) (ca (cm (ca (cm ((cz (4))) n) (cm ((cz (-4))) h)) m) (ca (cm ((cz (2))) (cp n 2)) (ca (cm ((cz (-4))) (cp h 2)) ((cz (48)))))))) c)) b) (ca (cm (ca (cm (ca (cm (ca (cm ((cz (-2))) n) (cm ((cz (4))) h)) n) ((cz (-48)))) c) (ca (cm (ca (cm ((cz (16))) n) (cm ((cz (-32))) h)) n) ((cz (384))))) c) (ca (cm (ca (cm ((cz (-2))) (cp n 2)) ((cz (48)))) l) (ca (cm (ca (cm (ca (cm ((cz (-2))) n) (cm ((cz (4))) h)) n) ((cz (-48)))) m) (ca (cm (ca (cm (ca (cm ((cz (-2))) n) (cm ((cz (2))) h)) n) (ca (cm ((cz (4))) (cp h 2)) ((cz (-48))))) n) (cm ((cz (-48))) h))))))

noncomputable def p10 (a b c l m n h : ℂ) : ℂ :=
  ca (cm (cm (ca (cm (ca (cm ((cz (-2))) b) (cm ((cz (2))) c)) b) (ca (cm ((cz (-2))) n) (cm ((cz (2))) h))) (cp b 3)) a) (cm (ca (cm (ca (cm (ca (cm (ca (cm ((cz (-2))) b) (ca (cm ((cz (-2))) c) ((cz (16))))) b) (ca (cm ((cz (-2))) l) (cm ((cz (2))) n))) b) (ca (cm (ca (cm ((cz (2))) l) (cm ((cz (2))) h)) c) ((cz (-96))))) b) (ca (cm (ca (cm ((cz (-2))) n) (cm ((cz (2))) h)) l) (ca (cm (cm ((cz (-2))) h) n) ((cz (48)))))) (cp b 2))

noncomputable def p11 (a b c l m n h : ℂ) : ℂ :=
  ca (cm (ca (cm (ca (cm (ca (cm (cm ((cz (-2))) (cp c 2)) a) (ca (cm (cm ((cz (-2))) (cp c 2)) b) (cm (ca (cm (ca (cm ((cz (-2))) c) ((cz (16)))) c) (ca (cm ((cz (-4))) m) (cm ((cz (-4))) h))) c))) a) (ca (cm (cm (ca (cm ((cz (6))) (cp c 2)) (ca (cm ((cz (-4))) m) (cm ((cz (-4))) h))) c) b) (ca (cm (ca (cm (ca (cm ((cz (-4))) (cp c 2)) (ca (cm ((cz (2))) l) (ca (cm ((cz (-2))) m) (cm ((cz (4))) n)))) c) (ca (cm ((cz (32))) m) (cm ((cz (32))) h))) c) (ca (cm (ca (cm ((cz (-2))) m) (cm ((cz (-4))) h)) m) ((cz (-48))))))) a) (ca (cm (ca (cm (ca (cm ((cz (-4))) (cp c 2)) (ca (cm ((cz (2))) m) (cm ((cz (6))) h))) (cp c 2)) (ca (cm (ca (cm ((cz (-2))) m) (cm ((cz (-4))) h)) m) ((cz (-48))))) b) (ca (cm (ca (cm (ca (cm (ca (cm (ca (cm ((cz (-4))) c) ((cz (32)))) c) (ca (cm ((cz (-2))) l) (ca (cm ((cz (-4))) n) (cm ((cz (-2))) h)))) c) ((cz (-288)))) c) (ca (cm (ca (cm ((cz (4))) m) (cm ((cz (4))) h)) l) (ca (cm ((cz (2))) (cp m 2)) (ca (cm (cm ((cz (4))) h) n) (ca (cm ((cz (-4))) (cp h 2)) ((cz (48)))))))) c) (ca (cm (ca (cm ((cz (16))) m) (cm ((cz (32))) h)) m) ((cz (384))))))) a) (ca (cm (cm (ca (cm (ca (cm ((cz (4))) m) (cm ((cz (-4))) h)) (cp c 2)) (ca (cm ((cz (-2))) (cp m 2)) ((cz (48))))) c) b) (ca (cm (ca (cm (ca (cm (ca (cm ((cz (4))) m) (cm ((cz (-4))) h)) c) (ca (cm ((cz (-32))) m) (cm ((cz (32))) h))) c) (ca (cm (ca (cm ((cz (-2))) m) (cm ((cz (-2))) h)) l) (ca (cm (ca (cm ((cz (4))) m) (ca (cm ((cz (4))) n) (cm ((cz (-2))) h))) m) (ca (cm (cm ((cz (-4))) h) n) (ca (cm ((cz (-4))) (cp h 2)) ((cz (48)))))))) (cp c 2)) (ca (cm (ca (cm (ca (cm ((cz (2))) m) (cm ((cz (4))) h)) m) ((cz (48)))) l) (ca (cm (ca (cm (ca (cm ((cz (2))) m) (ca (cm ((cz (-2))) n) (cm ((cz (2))) h))) m) (ca (cm ((cz (-4))) (cp h 2)) ((cz (48))))) m) (ca (cm ((cz (48))) n) (cm ((cz (-48))) h))))))

noncomputable def p12 (a b c l m n h : ℂ) : ℂ :=
  ca (cm (ca (cm (ca (cm (ca (cm (cm (cm ((cz (-12))) c) b) a) (ca (cm (ca (cm (cm ((cz (-28))) c) b) (ca (cm (ca (cm ((cz (-28))) c) ((cz (224)))) c) (ca (cm ((cz (-12))) m) (ca (cm ((cz (-8))) n) (cm ((cz (-4))) h))))) b) (cm (ca (cm ((cz (-12))) l) (ca (cm ((cz (8))) n) (cm ((cz (-4))) h))) c))) a) (ca (cm (ca (cm (ca (cm (cm ((cz (-28))) c) b) (ca (cm (ca (cm ((cz (-36))) c) ((cz (384)))) c) (ca (cm ((cz (-20))) m) (ca (cm ((cz (-20))) n) (cm ((cz (-8))) h))))) b) (ca (cm (ca (cm (ca (cm ((cz (-28))) c) ((cz (384)))) c) (ca (cm ((cz (-8))) l) (ca (cm ((cz (-8))) m) ((cz (-1536)))))) c) (ca (cm ((cz (160))) m) (ca (cm ((cz (128))) n) (cm ((cz (32))) h))))) b) (ca (cm (ca (cm (ca (cm ((cz (-20))) l) (ca (cm ((cz (20))) n) (cm ((cz (-8))) h))) c) (ca (cm ((cz (160))) l) (ca (cm ((cz (-128))) n) (cm ((cz (32))) h)))) c) (ca (cm (ca (cm ((cz (-12))) m) (ca (cm ((cz (-8))) n) (cm ((cz (-4))) h))) l) (ca (cm (ca (cm ((cz (8))) n) (cm ((cz (-4))) h)) m) (ca (cm ((cz (6))) (cp n 2)) (ca (cm ((cz (8))) (cp h 2)) ((cz (-48)))))))))) a) (ca (cm (ca (cm (ca (cm (ca (cm (cm ((cz (-12))) c) b) (ca (cm (ca (cm ((cz (-28))) c) ((cz (224)))) c) (ca (cm ((cz (-8))) m) (ca (cm ((cz (-12))) n) (cm ((cz (-4))) h))))) b) (ca (cm (ca (cm (ca (cm ((cz (-28))) c) ((cz (384)))) c) (ca (cm ((cz (8))) l) (ca (cm ((cz (-8))) n) ((cz (-1536)))))) c) (ca (cm ((cz (128))) m) (ca (cm ((cz (160))) n) (cm ((cz (32))) h))))) b) (ca (cm (ca (cm (ca (cm (ca (cm ((cz (-12))) c) ((cz (224)))) c) (ca (cm ((cz (8))) m) (ca (cm ((cz (8))) n) ((cz (-1536)))))) c) ((cz (3520)))) c) (ca (cm (ca (cm ((cz (12))) m) (ca (cm ((cz (12))) n) ((cz (-512))))) m) (ca (cm (ca (cm ((cz (12))) n) ((cz (-512)))) n) (ca (cm ((cz (8))) (cp h 2)) ((cz (-96)))))))) b) (ca (cm (ca (cm (ca (cm (ca (cm ((cz (-8))) l) (ca (cm ((cz (12))) n) (cm ((cz (-4))) h))) c) (ca (cm ((cz (128))) l) (ca (cm ((cz (-160))) n) (cm ((cz (32))) h)))) c) (ca (cm (ca (cm ((cz (12))) l) (ca (cm ((cz (-12))) n) ((cz (-512))))) l) (ca (cm (ca (cm ((cz (12))) n) ((cz (512)))) n) (ca (cm ((cz (8))) (cp h 2)) ((cz (-96))))))) c) (ca (cm (ca (cm ((cz (96))) m) (ca (cm ((cz (64))) n) (cm ((cz (32))) h))) l) (ca (cm (ca (cm ((cz (-64))) n) (cm ((cz (32))) h)) m) (ca (cm ((cz (-64))) (cp n 2)) (ca (cm ((cz (-64))) (cp h 2)) ((cz (768)))))))))) a) (ca (cm (ca (cm (ca (cm (cm (ca (cm ((cz (12))) l) (ca (cm ((cz (8))) m) (cm ((cz (-4))) h))) c) b) (ca (cm (ca (cm (ca (cm ((cz (20))) l) (ca (cm ((cz (20))) m) (cm ((cz (-8))) h))) c) (ca (cm ((cz (-160))) l) (ca (cm ((cz (-128))) m) (cm ((cz (32))) h)))) c) (ca (cm (ca (cm ((cz (8))) m) (ca (cm ((cz (12))) n) (cm ((cz (4))) h))) l) (ca (cm (ca (cm ((cz (6))) m) (cm ((cz (8))) n)) m) (ca (cm (cm ((cz (-4))) h) n) (ca (cm ((cz (8))) (cp h 2)) ((cz (-48))))))))) b) (ca (cm (ca (cm (ca (cm (ca (cm ((cz (8))) l) (ca (cm ((cz (12))) m) (cm ((cz (-4))) h))) c) (ca (cm ((cz (-128))) l) (ca (cm ((cz (-160))) m) (cm ((cz (32))) h)))) c) (ca (cm (ca (cm ((cz (12))) l) (ca (cm ((cz (12))) m) ((cz (512))))) l) (ca (cm (ca (cm ((cz (12))) m) ((cz (512)))) m) (ca (cm ((cz (8))) (cp h 2)) ((cz (-96))))))) c) (ca (cm (ca (cm ((cz (-64))) m) (ca (cm ((cz (-96))) n) (cm ((cz (-32))) h))) l) (ca (cm (ca (cm ((cz (-64))) m) (cm ((cz (-64))) n)) m) (ca (cm (cm ((cz (32))) h) n) (ca (cm ((cz (-64))) (cp h 2)) ((cz (768))))))))) b) (ca (cm (ca (cm (ca (cm (ca (cm ((cz (6))) l) (ca (cm ((cz (8))) m) (cm ((cz (-8))) n))) l) (ca (cm (ca (cm ((cz (-12))) n) (cm ((cz (4))) h)) m) (ca (cm (cm ((cz (4))) h) n) (ca (cm ((cz (8))) (cp h 2)) ((cz (-48))))))) c) (ca (cm (ca (cm ((cz (-64))) l) (ca (cm ((cz (-64))) m) (cm ((cz (64))) n))) l) (ca (cm (ca (cm ((cz (96))) n) (cm ((cz (-32))) h)) m) (ca (cm (cm ((cz (-32))) h) n) (ca (cm ((cz (-64))) (cp h 2)) ((cz (768)))))))) c) (ca (cm (ca (cm (ca (cm ((cz (12))) m) (ca (cm ((cz (12))) n) (cm ((cz (8))) h))) l) (ca (cm (ca (cm ((cz (12))) m) (cm ((cz (4))) h)) m) (cm (ca (cm ((cz (-12))) n) (cm ((cz (-4))) h)) n))) l) (ca (cm (ca (cm (ca (cm ((cz (-12))) n) (cm ((cz (8))) h)) m) (cm (ca (cm ((cz (-12))) n) (cm ((cz (4))) h)) n)) m) (ca (cm (cm ((cz (8))) h) (cp n 2)) (cm (ca (cm ((cz (16))) (cp h 2)) ((cz (-288)))) h))))))

noncomputable def p13 (a b c l m n h : ℂ) : ℂ :=
  ca (cm (ca (cm (ca (cm (ca (cm (cm ((cz (-2))) (cp b 2)) a) (cm (ca (cm (ca (cm ((cz (-2))) b) (ca (cm ((cz (-2))) c) ((cz (16))))) b) (ca (cm ((cz (-4))) l) (cm ((cz (-4))) h))) b)) a) (ca (cm (ca (cm (ca (cm (ca (cm ((cz (-4))) b) (cm ((cz (6))) c)) b) (ca (cm ((cz (-2))) l) (ca (cm ((cz (2))) m) (cm ((cz (-4))) n)))) b) (ca (cm (ca (cm ((cz (-4))) l) (cm ((cz (-4))) h)) c) (ca (cm ((cz (32))) l) (cm ((cz (32))) h)))) b) (ca (cm (ca (cm ((cz (-2))) l) (cm ((cz (-4))) h)) l) ((cz (-48)))))) a) (ca (cm (ca (cm (ca (cm (ca (cm (ca (cm ((cz (-4))) b) (ca (cm ((cz (-4))) c) ((cz (32))))) b) (ca (cm ((cz (-2))) m) (ca (cm ((cz (4))) n) (cm ((cz (-2))) h)))) b) (ca (cm (ca (cm ((cz (2))) l) (cm ((cz (6))) h)) c) ((cz (-288))))) b) (ca (cm (ca (cm ((cz (2))) l) (cm ((cz (4))) m)) l) (ca (cm (cm ((cz (4))) h) m) (ca (cm (cm ((cz (-4))) h) n) (ca (cm ((cz (-4))) (cp h 2)) ((cz (48)))))))) b) (ca (cm (ca (cm (ca (cm ((cz (-2))) l) (cm ((cz (-4))) h)) l) ((cz (-48)))) c) (ca (cm (ca (cm ((cz (16))) l) (cm ((cz (32))) h)) l) ((cz (384))))))) a) (ca (cm (ca (cm (ca (cm (ca (cm (ca (cm ((cz (4))) l) (cm ((cz (-4))) h)) b) (ca (cm (ca (cm ((cz (4))) l) (cm ((cz (-4))) h)) c) (ca (cm ((cz (-32))) l) (cm ((cz (32))) h)))) b) (ca (cm (ca (cm ((cz (4))) l) (ca (cm ((cz (-2))) m) (ca (cm ((cz (-4))) n) (cm ((cz (-2))) h)))) l) (ca (cm (cm ((cz (-2))) h) m) (ca (cm (cm ((cz (4))) h) n) (ca (cm ((cz (-4))) (cp h 2)) ((cz (48)))))))) b) (cm (ca (cm ((cz (-2))) (cp l 2)) ((cz (48)))) c)) b) (ca (cm (ca (cm (ca (cm ((cz (2))) l) (ca (cm ((cz (2))) m) (ca (cm ((cz (2))) n) (cm ((cz (2))) h)))) l) (ca (cm (cm ((cz (4))) h) m) (ca (cm ((cz (-4))) (cp h 2)) ((cz (48)))))) l) (ca (cm ((cz (48))) m) (ca (cm ((cz (-48))) n) (cm ((cz (-48))) h)))))

noncomputable def p14 (a b c l m n h : ℂ) : ℂ :=
  ca (cm (ca (cm (ca (cm (ca (cm (ca (cm (cm ((cz (-4))) c) a) (ca (cm (cm ((cz (-4))) c) b) (ca (cm (ca (cm ((cz (-4))) c) ((cz (32)))) c) (ca (cm ((cz (-4))) m) (cm ((cz (-4))) h))))) a) (ca (cm (ca (cm ((cz (6))) (cp c 2)) (ca (cm ((cz (-4))) m) (cm ((cz (-4))) h))) b) (ca (cm (ca (cm ((cz (-2))) (cp c 2)) (ca (cm ((cz (4))) l) (ca (cm ((cz (2))) n) (cm ((cz (-2))) h)))) c) (ca (cm ((cz (32))) m) (cm ((cz (32))) h))))) a) (ca (cm (cm (ca (cm ((cz (-2))) (cp c 2)) (ca (cm ((cz (-2))) m) (cm ((cz (6))) h))) c) b) (ca (cm (ca (cm (ca (cm (ca (cm ((cz (-2))) c) ((cz (16)))) c) (ca (cm ((cz (-4))) l) (ca (cm ((cz (2))) m) (cm ((cz (-2))) n)))) c) ((cz (-288)))) c) (ca (cm (ca (cm ((cz (4))) m) (cm ((cz (4))) h)) l) (ca (cm (ca (cm ((cz (4))) m) (ca (cm ((cz (-2))) n) (cm ((cz (2))) h))) m) (ca (cm (cm ((cz (2))) h) n) (ca (cm ((cz (-4))) (cp h 2)) ((cz (48)))))))))) a) (ca (cm (ca (cm (ca (cm ((cz (4))) m) (cm ((cz (-4))) h)) (cp c 2)) (ca (cm ((cz (-2))) (cp m 2)) ((cz (48))))) b) (cm (ca (cm (ca (cm (ca (cm ((cz (4))) m) (cm ((cz (-4))) h)) c) (ca (cm ((cz (-32))) m) (cm ((cz (32))) h))) c) (ca (cm (cm ((cz (-4))) h) l) (ca (cm (ca (cm ((cz (2))) m) (cm ((cz (4))) n)) m) (ca (cm (cm ((cz (-4))) h) n) (ca (cm ((cz (-4))) (cp h 2)) ((cz (48)))))))) c))) a) (ca (cm (cm (ca (cm (ca (cm ((cz (-2))) m) (cm ((cz (4))) h)) m) ((cz (-48)))) c) b) (ca (cm (ca (cm (ca (cm (ca (cm ((cz (-2))) m) (cm ((cz (4))) h)) m) ((cz (-48)))) c) (ca (cm (ca (cm ((cz (16))) m) (cm ((cz (-32))) h)) m) ((cz (384))))) c) (ca (cm (ca (cm ((cz (2))) (cp m 2)) ((cz (-48)))) l) (ca (cm (ca (cm (ca (cm ((cz (-2))) m) (ca (cm ((cz (-2))) n) (cm ((cz (2))) h))) m) (ca (cm (cm ((cz (4))) h) n) (ca (cm ((cz (4))) (cp h 2)) ((cz (-48)))))) m) (ca (cm ((cz (-48))) n) (cm ((cz (-48))) h))))))

noncomputable def p15 (a b c l m n h : ℂ) : ℂ :=
  ca (cm (ca (cm (ca (cm (ca (cm (ca (cm (cm ((cz (-4))) b) a) (ca (cm (ca (cm ((cz (-4))) b) (ca (cm ((cz (-4))) c) ((cz (32))))) b) (ca (cm ((cz (-4))) l) (cm ((cz (-4))) h)))) a) (ca (cm (ca (cm (ca (cm ((cz (-2))) b) (cm ((cz (6))) c)) b) (ca (cm ((cz (4))) m) (ca (cm ((cz (-2))) n) (cm ((cz (-2))) h)))) b) (ca (cm (ca (cm ((cz (-4))) l) (cm ((cz (-4))) h)) c) (ca (cm ((cz (32))) l) (cm ((cz (32))) h))))) a) (ca (cm (ca (cm (ca (cm (ca (cm ((cz (-2))) b) (ca (cm ((cz (-2))) c) ((cz (16))))) b) (ca (cm ((cz (2))) l) (ca (cm ((cz (-4))) m) (cm ((cz (2))) n)))) b) (ca (cm (ca (cm ((cz (-2))) l) (cm ((cz (6))) h)) c) ((cz (-288))))) b) (ca (cm (ca (cm ((cz (4))) l) (ca (cm ((cz (4))) m) (ca (cm ((cz (2))) n) (cm ((cz (2))) h)))) l) (ca (cm (cm ((cz (4))) h) m) (ca (cm (cm ((cz (-2))) h) n) (ca (cm ((cz (-4))) (cp h 2)) ((cz (48))))))))) a) (ca (cm (ca (cm (ca (cm (ca (cm ((cz (4))) l) (cm ((cz (-4))) h)) b) (ca (cm (ca (cm ((cz (4))) l) (cm ((cz (-4))) h)) c) (ca (cm ((cz (-32))) l) (cm ((cz (32))) h)))) b) (ca (cm (ca (cm ((cz (2))) l) (cm ((cz (-4))) n)) l) (ca (cm (cm ((cz (-4))) h) m) (ca (cm (cm ((cz (4))) h) n) (ca (cm ((cz (-4))) (cp h 2)) ((cz (48)))))))) b) (cm (ca (cm ((cz (-2))) (cp l 2)) ((cz (48)))) c))) a) (ca (cm (ca (cm (ca (cm (ca (cm ((cz (-2))) l) (cm ((cz (4))) h)) l) ((cz (-48)))) b) (ca (cm (ca (cm (ca (cm ((cz (-2))) l) (cm ((cz (4))) h)) l) ((cz (-48)))) c) (ca (cm (ca (cm ((cz (16))) l) (cm ((cz (-32))) h)) l) ((cz (384)))))) b) (ca (cm (ca (cm (ca (cm ((cz (-2))) l) (ca (cm ((cz (2))) m) (ca (cm ((cz (2))) n) (cm ((cz (2))) h)))) l) (ca (cm (cm ((cz (-4))) h) n) (ca (cm ((cz (4))) (cp h 2)) ((cz (-48)))))) l) (ca (cm ((cz (-48))) m) (ca (cm ((cz (48))) n) (cm ((cz (-48))) h)))))

noncomputable def p16 (a b c l m n h : ℂ) : ℂ :=
  cm (ca (cm (ca (cm (ca (cm (ca (cm ((cz (-2))) a) (ca (cm ((cz (-2))) b) (ca (cm ((cz (-2))) c) ((cz (16)))))) a) (ca (cm (cm ((cz (2))) c) b) (ca (cm ((cz (2))) l) (cm ((cz (2))) m)))) a) (ca (cm (ca (cm ((cz (-2))) m) (cm ((cz (2))) h)) b) (ca (cm (ca (cm ((cz (-2))) l) (cm ((cz (2))) h)) c) ((cz (-96)))))) a) (ca (cm (ca (cm ((cz (2))) m) (cm ((cz (-2))) h)) l) (ca (cm (cm ((cz (-2))) h) m) ((cz (48)))))) (cp a 2)

noncomputable def p17 (a b c l m n h : ℂ) : ℂ :=
  ca (cm (ca (cm (ca (cm (ca (cm ((cz (4))) b) (cm ((cz (-4))) c)) a) (ca (cm (ca (cm ((cz (8))) b) (ca (cm ((cz (4))) c) ((cz (-64))))) b) (ca (cm (ca (cm ((cz (-4))) c) ((cz (32)))) c) (ca (cm ((cz (4))) l) (ca (cm ((cz (-4))) m) (ca (cm ((cz (-4))) n) (cm ((cz (4))) h))))))) a) (ca (cm (ca (cm (ca (cm ((cz (4))) b) (ca (cm ((cz (4))) c) ((cz (-64))))) b) (ca (cm (ca (cm ((cz (4))) c) ((cz (-64)))) c) (ca (cm ((cz (-8))) m) (ca (cm ((cz (-8))) n) (ca (cm ((cz (8))) h) ((cz (256)))))))) b) (ca (cm (ca (cm ((cz (-4))) (cp c 2)) (ca (cm ((cz (8))) l) (cm ((cz (-4))) n))) c) (ca (cm ((cz (-32))) l) (ca (cm ((cz (32))) m) (ca (cm ((cz (32))) n) (cm ((cz (-32))) h))))))) a) (ca (cm (ca (cm (ca (cm (cm ((cz (-4))) c) b) (ca (cm (ca (cm ((cz (-4))) c) ((cz (32)))) c) (ca (cm ((cz (-4))) l) (ca (cm ((cz (-4))) m) (ca (cm ((cz (-4))) n) (cm ((cz (4))) h)))))) b) (ca (cm (ca (cm ((cz (-4))) (cp c 2)) (ca (cm ((cz (-8))) l) (cm ((cz (-4))) m))) c) (ca (cm ((cz (32))) l) (ca (cm ((cz (32))) m) (ca (cm ((cz (32))) n) (cm ((cz (-32))) h)))))) b) (ca (cm (ca (cm (ca (cm ((cz (-4))) c) ((cz (32)))) c) (ca (cm ((cz (-4))) m) (ca (cm ((cz (-4))) n) (cm ((cz (-4))) h)))) (cp c 2)) (ca (cm ((cz (-4))) (cp l 2)) (ca (cm (ca (cm ((cz (4))) m) (ca (cm ((cz (4))) n) (cm ((cz (-8))) h))) m) (ca (cm (ca (cm ((cz (4))) n) (cm ((cz (-8))) h)) n) (cm ((cz (4))) (cp h 2)))))))

noncomputable def p18 (a b c l m n h : ℂ) : ℂ :=
  ca (cm (ca (cm (ca (cm (ca (cm ((cz (-4))) b) (cm ((cz (4))) c)) a) (ca (cm (ca (cm ((cz (-4))) b) (ca (cm ((cz (4))) c) ((cz (32))))) b) (ca (cm (ca (cm ((cz (8))) c) ((cz (-64)))) c) (ca (cm ((cz (-4))) l) (ca (cm ((cz (4))) m) (ca (cm ((cz (4))) n) (cm ((cz (4))) h))))))) a) (ca (cm (ca (cm (ca (cm ((cz (-4))) b) (cm ((cz (4))) c)) b) (ca (cm (ca (cm ((cz (4))) c) ((cz (-64)))) c) (ca (cm ((cz (8))) m) (cm ((cz (4))) n)))) b) (ca (cm (ca (cm (ca (cm ((cz (4))) c) ((cz (-64)))) c) (ca (cm ((cz (-8))) l) (ca (cm ((cz (8))) n) (ca (cm ((cz (8))) h) ((cz (256))))))) c) (ca (cm ((cz (32))) l) (ca (cm ((cz (-32))) m) (ca (cm ((cz (-32))) n) (cm ((cz (-32))) h))))))) a) (ca (cm (ca (cm (ca (cm (ca (cm ((cz (-4))) b) (ca (cm ((cz (-4))) c) ((cz (32))))) b) (ca (cm ((cz (-4))) (cp c 2)) (ca (cm ((cz (-4))) l) (ca (cm ((cz (4))) n) (cm ((cz (-4))) h))))) b) (cm (ca (cm (ca (cm ((cz (-4))) c) ((cz (32)))) c) (ca (cm ((cz (-4))) l) (cm ((cz (-8))) m))) c)) b) (ca (cm (ca (cm (ca (cm ((cz (-4))) l) (ca (cm ((cz (-4))) m) (ca (cm ((cz (4))) n) (cm ((cz (4))) h)))) c) (ca (cm ((cz (32))) l) (ca (cm ((cz (32))) m) (ca (cm ((cz (-32))) n) (cm ((cz (-32))) h))))) c) (ca (cm (ca (cm ((cz (4))) l) (ca (cm ((cz (-4))) n) (cm ((cz (-8))) h))) l) (ca (cm ((cz (-4))) (cp m 2)) (ca (cm (ca (cm ((cz (4))) n) (cm ((cz (8))) h)) n) (cm ((cz (4))) (cp h 2)))))))

noncomputable def p19 (a b c l m n h : ℂ) : ℂ :=
  ca (cm (ca (cm (ca (cm (ca (cm ((cz (-4))) a) (ca (cm ((cz (-4))) b) (ca (cm ((cz (-4))) c) ((cz (32)))))) a) (ca (cm (ca (cm ((cz (-4))) b) (cm ((cz (4))) c)) b) (ca (cm ((cz (-4))) (cp c 2)) (ca (cm ((cz (4))) l) (ca (cm ((cz (4))) m) (cm ((cz (-4))) h)))))) a) (ca (cm (ca (cm (ca (cm ((cz (-4))) b) (ca (cm ((cz (4))) c) ((cz (32))))) b) (ca (cm (ca (cm ((cz (4))) c) ((cz (-64)))) c) (ca (cm ((cz (4))) m) (cm ((cz (8))) n)))) b) (cm (ca (cm (ca (cm ((cz (-4))) c) ((cz (32)))) c) (ca (cm ((cz (4))) l) (cm ((cz (-8))) n))) c))) a) (ca (cm (ca (cm (ca (cm (cm ((cz (4))) c) b) (ca (cm (ca (cm ((cz (8))) c) ((cz (-64)))) c) (ca (cm ((cz (4))) l) (ca (cm ((cz (4))) m) (ca (cm ((cz (4))) n) (cm ((cz (4))) h)))))) b) (ca (cm (ca (cm (ca (cm ((cz (4))) c) ((cz (-64)))) c) (ca (cm ((cz (8))) l) (ca (cm ((cz (8))) m) (ca (cm ((cz (8))) h) ((cz (256))))))) c) (ca (cm ((cz (-32))) l) (ca (cm ((cz (-32))) m) (ca (cm ((cz (-32))) n) (cm ((cz (-32))) h)))))) b) (ca (cm (ca (cm (ca (cm ((cz (4))) l) (ca (cm ((cz (4))) m) (ca (cm ((cz (-4))) n) (cm ((cz (4))) h)))) c) (ca (cm ((cz (-32))) l) (ca (cm ((cz (-32))) m) (ca (cm ((cz (32))) n) (cm ((cz (-32))) h))))) c) (ca (cm (ca (cm ((cz (4))) l) (ca (cm ((cz (4))) m) (cm ((cz (8))) h))) l) (ca (cm (ca (cm ((cz (4))) m) (cm ((cz (8))) h)) m) (ca (cm ((cz (-4))) (cp n 2)) (cm ((cz (4))) (cp h 2)))))))


lemma sum_perm_succ {n : ℕ} (g : Equiv.Perm (Fin (n + 1)) → ℂ) :
    ∑ σ, g σ = ∑ a : Fin (n + 1), ∑ τ : Equiv.Perm (Fin n),
      g (Equiv.Perm.decomposeFin.symm (a, τ)) := by
  rw [← Equiv.Perm.decomposeFin.symm.sum_comp, Fintype.sum_prod_type]

lemma perm4 (M : Matrix (Fin 4) (Fin 4) ℂ) : Matrix.permanent M =
    (M 0 0 * M 1 1 + M 0 1 * M 1 0) * (M 2 2 * M 3 3 + M 2 3 * M 3 2) + (M 0 0 * M 1 2 + M 0 2 * M 1 0) * (M 2 1 * M 3 3 + M 2 3 * M 3 1) + (M 0 0 * M 1 3 + M 0 3 * M 1 0) * (M 2 1 * M 3 2 + M 2 2 * M 3 1) + (M 0 1 * M 1 2 + M 0 2 * M 1 1) * (M 2 0 * M 3 3 + M 2 3 * M 3 0) + (M 0 1 * M 1 3 + M 0 3 * M 1 1) * (M 2 0 * M 3 2 + M 2 2 * M 3 0) + (M 0 2 * M 1 3 + M 0 3 * M 1 2) * (M 2 0 * M 3 1 + M 2 1 * M 3 0) := by
  simp only [Matrix.permanent]
  rw [sum_perm_succ]
  simp only [sum_perm_succ (n := 2), sum_perm_succ (n := 1), sum_perm_succ (n := 0)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.prod_univ_succ, Fin.prod_univ_zero,
    Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ,
    Fintype.sum_unique]
  simp +decide [Equiv.swap_apply_def]
  ring


noncomputable def model (a b c l m n h x y z : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![(0 : ℂ), cm (cm ((cz (1))) x) h, cm (cm ((cz (1))) y) h, cm (cm ((cz (1))) z) h], ![cm (cm ((cz (1))) x) h, ca (cm (ca (cm (cm ((cz (-2))) x) a) (ca (cm (cm ((cz (-2))) x) b) (ca (cm (cm ((cz (-2))) x) c) (cm ((cz (16))) x)))) a) (ca (cm (cm ((cz (2))) x) l) (ca (cm (cm ((cz (2))) x) m) (cm (cm ((cz (-2))) x) h))), ca (cm (cm (cm ((cz (1))) x) c) a) (ca (cm (cm (cm ((cz (1))) y) c) b) (ca (cm (cm ((cz (1))) z) (cp c 2)) (ca (cm (cm ((cz (-1))) x) m) (cm (cm ((cz (-1))) y) n)))), ca (cm (cm (cm ((cz (1))) x) b) a) (ca (cm (ca (cm (cm ((cz (1))) y) b) (cm (cm ((cz (1))) z) c)) b) (ca (cm (cm ((cz (-1))) x) l) (cm (cm ((cz (1))) z) n)))], ![cm (cm ((cz (1))) y) h, ca (cm (cm (cm ((cz (1))) x) c) a) (ca (cm (cm (cm ((cz (1))) y) c) b) (ca (cm (cm ((cz (1))) z) (cp c 2)) (ca (cm (cm ((cz (-1))) x) m) (cm (cm ((cz (-1))) y) n)))), ca (cm (cm (cm ((cz (-2))) y) b) a) (ca (cm (ca (cm (cm ((cz (-2))) y) b) (ca (cm (cm ((cz (-2))) y) c) (cm ((cz (16))) y))) b) (ca (cm (cm ((cz (-2))) y) l) (ca (cm (cm ((cz (2))) y) n) (cm (cm ((cz (-2))) y) h)))), ca (cm (ca (cm (cm ((cz (1))) x) a) (ca (cm (cm ((cz (1))) y) b) (cm (cm ((cz (1))) z) c))) a) (ca (cm (cm ((cz (1))) y) l) (cm (cm ((cz (1))) z) m))], ![cm (cm ((cz (1))) z) h, ca (cm (cm (cm ((cz (1))) x) b) a) (ca (cm (ca (cm (cm ((cz (1))) y) b) (cm (cm ((cz (1))) z) c)) b) (ca (cm (cm ((cz (-1))) x) l) (cm (cm ((cz (1))) z) n))), ca (cm (ca (cm (cm ((cz (1))) x) a) (ca (cm (cm ((cz (1))) y) b) (cm (cm ((cz (1))) z) c))) a) (ca (cm (cm ((cz (1))) y) l) (cm (cm ((cz (1))) z) m)), ca (cm (cm (cm ((cz (-2))) z) c) a) (ca (cm (cm (cm ((cz (-2))) z) c) b) (ca (cm (ca (cm (cm ((cz (-2))) z) c) (cm ((cz (16))) z)) c) (ca (cm (cm ((cz (-2))) z) m) (ca (cm (cm ((cz (-2))) z) n) (cm (cm ((cz (-2))) z) h)))))]]

noncomputable def quad (a b c l m n h x y z : ℂ) : ℂ :=
  (p1 a b c l m n h) * x ^ 0 * y ^ 0 * z ^ 2 + (p2 a b c l m n h) * x ^ 0 * y ^ 1 * z ^ 1 + (p3 a b c l m n h) * x ^ 0 * y ^ 2 * z ^ 0 + (p4 a b c l m n h) * x ^ 1 * y ^ 0 * z ^ 1 + (p5 a b c l m n h) * x ^ 1 * y ^ 1 * z ^ 0 + (p6 a b c l m n h) * x ^ 2 * y ^ 0 * z ^ 0

noncomputable def cubic (a b c l m n h x y z : ℂ) : ℂ :=
  (p7 a b c l m n h) * x ^ 0 * y ^ 0 * z ^ 3 + (p8 a b c l m n h) * x ^ 0 * y ^ 1 * z ^ 2 + (p9 a b c l m n h) * x ^ 0 * y ^ 2 * z ^ 1 + (p10 a b c l m n h) * x ^ 0 * y ^ 3 * z ^ 0 + (p11 a b c l m n h) * x ^ 1 * y ^ 0 * z ^ 2 + (p12 a b c l m n h) * x ^ 1 * y ^ 1 * z ^ 1 + (p13 a b c l m n h) * x ^ 1 * y ^ 2 * z ^ 0 + (p14 a b c l m n h) * x ^ 2 * y ^ 0 * z ^ 1 + (p15 a b c l m n h) * x ^ 2 * y ^ 1 * z ^ 0 + (p16 a b c l m n h) * x ^ 3 * y ^ 0 * z ^ 0

noncomputable def bracket (a b c l m n h x y z : ℂ) : ℂ :=
  p17 a b c l m n h * z + p18 a b c l m n h * y + p19 a b c l m n h * x

noncomputable def correction (a b c l m n h x y z w : ℂ) : ℂ :=
  ca (cm (ca (cm (ca (cm (ca (cm (cm (cm ((cz (1))) (cp w 4)) (cp x 4)) a) (ca (cm (cm (cm (cm ((cz (4))) (cp w 4)) y) (cp x 3)) b) (cm (cm (cm (cm ((cz (4))) (cp w 4)) z) (cp x 3)) c))) a) (ca (cm (ca (cm (cm (cm (cm ((cz (6))) (cp w 4)) (cp y 2)) (cp x 2)) b) (cm (cm (cm (cm (cm ((cz (12))) (cp w 4)) z) y) (cp x 2)) c)) b) (ca (cm (cm (cm (cm ((cz (6))) (cp w 4)) (cp z 2)) (cp x 2)) (cp c 2)) (cm (cm (ca (cm (ca (cm (cm ((cz (2))) (cp w 3)) x) (ca (cm (cm ((cz (2))) (cp w 3)) y) (cm (cm ((cz (2))) (cp w 3)) z))) x) (ca (cm (ca (cm (cm ((cz (-2))) (cp w 3)) y) (cm (cm ((cz (-2))) (cp w 3)) z)) y) (cm (cm ((cz (-2))) (cp w 3)) (cp z 2)))) x) h)))) a) (ca (cm (ca (cm (ca (cm (cm (cm (cm ((cz (4))) (cp w 4)) (cp y 3)) x) b) (cm (cm (cm (cm (cm ((cz (12))) (cp w 4)) z) (cp y 2)) x) c)) b) (ca (cm (cm (cm (cm (cm ((cz (12))) (cp w 4)) (cp z 2)) y) x) (cp c 2)) (cm (ca (cm (ca (cm (ca (cm (cm ((cz (2))) (cp w 3)) y) (cm (cm ((cz (2))) (cp w 3)) z)) x) (ca (cm (ca (cm (cm ((cz (2))) (cp w 3)) y) (cm (cm ((cz (-4))) (cp w 3)) z)) y) (cm (cm ((cz (-2))) (cp w 3)) (cp z 2)))) x) (cm (ca (cm (cm (cm ((cz (2))) (cp w 3)) z) y) (cm (cm ((cz (-2))) (cp w 3)) (cp z 2))) y)) h))) b) (ca (cm (ca (cm (cm (cm (cm ((cz (4))) (cp w 4)) (cp z 3)) x) (cp c 2)) (cm (ca (cm (ca (cm (ca (cm (cm ((cz (2))) (cp w 3)) y) (cm (cm ((cz (2))) (cp w 3)) z)) x) (ca (cm (ca (cm (cm ((cz (-2))) (cp w 3)) y) (cm (cm ((cz (-4))) (cp w 3)) z)) y) (cm (cm ((cz (2))) (cp w 3)) (cp z 2)))) x) (cm (ca (cm (cm (cm ((cz (-2))) (cp w 3)) z) y) (cm (cm ((cz (2))) (cp w 3)) (cp z 2))) y)) h)) c) (cm (cm (ca (cm (ca (cm (cm ((cz (16))) (cp w 3)) y) (cm (cm ((cz (32))) (cp w 3)) z)) y) (cm (cm ((cz (16))) (cp w 3)) (cp z 2))) x) h)))) a) (ca (cm (ca (cm (ca (cm (ca (cm (cm (cm ((cz (1))) (cp w 4)) (cp y 4)) b) (cm (cm (cm (cm ((cz (4))) (cp w 4)) z) (cp y 3)) c)) b) (ca (cm (cm (cm (cm ((cz (6))) (cp w 4)) (cp z 2)) (cp y 2)) (cp c 2)) (cm (ca (cm (ca (cm (cm (cm ((cz (-2))) (cp w 3)) y) x) (cm (ca (cm (cm ((cz (2))) (cp w 3)) y) (cm (cm ((cz (-2))) (cp w 3)) z)) y)) x) (cm (ca (cm (ca (cm (cm ((cz (2))) (cp w 3)) y) (cm (cm ((cz (2))) (cp w 3)) z)) y) (cm (cm ((cz (-2))) (cp w 3)) (cp z 2))) y)) h))) b) (ca (cm (ca (cm (cm (cm (cm ((cz (4))) (cp w 4)) (cp z 3)) y) (cp c 2)) (cm (ca (cm (ca (cm (ca (cm (cm ((cz (-2))) (cp w 3)) y) (cm (cm ((cz (-2))) (cp w 3)) z)) x) (ca (cm (ca (cm (cm ((cz (2))) (cp w 3)) y) (cm (cm ((cz (-4))) (cp w 3)) z)) y) (cm (cm ((cz (2))) (cp w 3)) (cp z 2)))) x) (cm (ca (cm (cm (cm ((cz (2))) (cp w 3)) z) y) (cm (cm ((cz (2))) (cp w 3)) (cp z 2))) y)) h)) c) (cm (ca (cm (ca (cm (cm (cm ((cz (16))) (cp w 3)) y) x) (cm (cm (cm ((cz (32))) (cp w 3)) z) y)) x) (cm (cm (cm ((cz (16))) (cp w 3)) (cp z 2)) y)) h))) b) (ca (cm (ca (cm (ca (cm (cm (cm ((cz (1))) (cp w 4)) (cp z 4)) (cp c 2)) (cm (ca (cm (ca (cm (cm (cm ((cz (-2))) (cp w 3)) z) x) (ca (cm (cm (cm ((cz (-2))) (cp w 3)) z) y) (cm (cm ((cz (2))) (cp w 3)) (cp z 2)))) x) (ca (cm (ca (cm (cm (cm ((cz (-2))) (cp w 3)) z) y) (cm (cm ((cz (2))) (cp w 3)) (cp z 2))) y) (cm (cm ((cz (2))) (cp w 3)) (cp z 3)))) h)) c) (cm (ca (cm (ca (cm (cm (cm ((cz (16))) (cp w 3)) z) x) (cm (cm (cm ((cz (32))) (cp w 3)) z) y)) x) (cm (cm (cm ((cz (16))) (cp w 3)) z) (cp y 2))) h)) c) (ca (cm (cm (ca (cm (ca (cm (ca (cm (cm ((cz (-2))) (cp w 3)) y) (cm (cm ((cz (-2))) (cp w 3)) z)) x) (ca (cm (cm ((cz (2))) (cp w 3)) (cp y 2)) (cm (cm ((cz (2))) (cp w 3)) (cp z 2)))) x) (cm (ca (cm (cm (cm ((cz (2))) (cp w 3)) z) y) (cm (cm ((cz (-2))) (cp w 3)) (cp z 2))) y)) h) l) (ca (cm (cm (ca (cm (ca (cm (ca (cm (cm ((cz (-2))) (cp w 3)) y) (cm (cm ((cz (-2))) (cp w 3)) z)) x) (ca (cm (cm ((cz (2))) (cp w 3)) (cp y 2)) (cm (cm ((cz (2))) (cp w 3)) (cp z 2)))) x) (cm (ca (cm (cm (cm ((cz (-2))) (cp w 3)) z) y) (cm (cm ((cz (2))) (cp w 3)) (cp z 2))) y)) h) m) (ca (cm (cm (ca (cm (ca (cm (ca (cm (cm ((cz (2))) (cp w 3)) y) (cm (cm ((cz (-2))) (cp w 3)) z)) x) (ca (cm (cm ((cz (-2))) (cp w 3)) (cp y 2)) (cm (cm ((cz (2))) (cp w 3)) (cp z 2)))) x) (cm (ca (cm (cm (cm ((cz (-2))) (cp w 3)) z) y) (cm (cm ((cz (2))) (cp w 3)) (cp z 2))) y)) h) n) (cm (ca (cm (ca (cm (ca (cm (cm ((cz (-2))) (cp w 3)) y) (ca (cm (cm ((cz (-2))) (cp w 3)) z) (cm ((cz (2))) (cp w 2)))) x) (ca (cm (ca (cm (cm ((cz (-2))) (cp w 3)) y) (ca (cm (cm ((cz (-12))) (cp w 3)) z) (cm ((cz (4))) (cp w 2)))) y) (cm (ca (cm (cm ((cz (-2))) (cp w 3)) z) (cm ((cz (4))) (cp w 2))) z))) x) (ca (cm (ca (cm (ca (cm (cm ((cz (-2))) (cp w 3)) z) (cm ((cz (2))) (cp w 2))) y) (cm (ca (cm (cm ((cz (-2))) (cp w 3)) z) (cm ((cz (4))) (cp w 2))) z)) y) (cm (cm ((cz (2))) (cp w 2)) (cp z 2)))) (cp h 2)))))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem permanent_expansion (a b c l m n h x y z w : ℂ) (hk : h ^ 2 = 24) :
    Matrix.permanent (Matrix.of fun i j => h + w * model a b c l m n h x y z i j) - 24 * (h + w * (a*x+b*y+c*z)) ^ 4 =
      h ^ 2 * w ^ 2 * quad a b c l m n h x y z + h * w ^ 3 * cubic a b c l m n h x y z +
      h ^ 2 * w ^ 4 * x * y * z * bracket a b c l m n h x y z := by
  rw [perm4]
  simp [Matrix.of_apply, model]
  linear_combination (norm := skip) (correction a b c l m n h x y z w) * hk
  simp only [quad, cubic, bracket, correction, p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, ca, cm, cp, cz]
  ring

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 10000 in
theorem extract_equations (a b c l m n h : ℂ) (hk : h ^ 2 = 24)
    (H : ∀ x y z w : ℂ, h ^ 2 * w ^ 2 * quad a b c l m n h x y z + h * w ^ 3 * cubic a b c l m n h x y z + h ^ 2 * w ^ 4 * x * y * z * bracket a b c l m n h x y z = 0) :
    p0 a b c l m n h = 0 ∧
    p1 a b c l m n h = 0 ∧
    p2 a b c l m n h = 0 ∧
    p3 a b c l m n h = 0 ∧
    p4 a b c l m n h = 0 ∧
    p5 a b c l m n h = 0 ∧
    p6 a b c l m n h = 0 ∧
    p7 a b c l m n h = 0 ∧
    p8 a b c l m n h = 0 ∧
    p9 a b c l m n h = 0 ∧
    p10 a b c l m n h = 0 ∧
    p11 a b c l m n h = 0 ∧
    p12 a b c l m n h = 0 ∧
    p13 a b c l m n h = 0 ∧
    p14 a b c l m n h = 0 ∧
    p15 a b c l m n h = 0 ∧
    p16 a b c l m n h = 0 ∧
    p17 a b c l m n h = 0 ∧
    p18 a b c l m n h = 0 ∧
    p19 a b c l m n h = 0 := by
  have hn : h ≠ 0 := by
    intro hz
    rw [hz] at hk
    norm_num at hk
  have hq : ∀ x y z : ℂ, quad a b c l m n h x y z = 0 := by
    intro x y z
    have u1 := H x y z 1
    have un1 := H x y z (-1)
    have u2 := H x y z 2
    have un2 := H x y z (-2)
    have hs : h ^ 2 * (quad a b c l m n h x y z) = 0 := by
      linear_combination (2 / 3 : ℂ) * u1 + (2 / 3 : ℂ) * un1 - (1 / 24 : ℂ) * u2 - (1 / 24 : ℂ) * un2
    rw [hk] at hs
    linear_combination (1 / 24 : ℂ) * hs
  have hc : ∀ x y z : ℂ, cubic a b c l m n h x y z = 0 := by
    intro x y z
    have u1 := H x y z 1
    have un1 := H x y z (-1)
    have u2 := H x y z 2
    have un2 := H x y z (-2)
    have hs : h * cubic a b c l m n h x y z = 0 := by
      linear_combination (-1 / 6 : ℂ) * u1 + (1 / 6 : ℂ) * un1 + (1 / 12 : ℂ) * u2 - (1 / 12 : ℂ) * un2
    exact (mul_eq_zero.mp hs).resolve_left hn
  have hr : ∀ x y z : ℂ, x * y * z * bracket a b c l m n h x y z = 0 := by
    intro x y z
    have u1 := H x y z 1
    have un1 := H x y z (-1)
    have u2 := H x y z 2
    have un2 := H x y z (-2)
    have hs : h ^ 2 * (x * y * z * bracket a b c l m n h x y z) = 0 := by
      linear_combination (1 / 24 : ℂ) * (u2 + un2 - 4 * u1 - 4 * un1)
    rw [hk] at hs
    linear_combination (1 / 24 : ℂ) * hs
  have q001 := hq 0 0 1
  have q010 := hq 0 1 0
  have q100 := hq 1 0 0
  have q011 := hq 0 1 1
  have q101 := hq 1 0 1
  have q110 := hq 1 1 0
  simp only [quad] at q001 q010 q100 q011 q101 q110
  have c001 := hc 0 0 1
  have c010 := hc 0 1 0
  have c100 := hc 1 0 0
  have c011 := hc 0 1 1
  have c01n1 := hc 0 1 (-1)
  have c101 := hc 1 0 1
  have c10n1 := hc 1 0 (-1)
  have c110 := hc 1 1 0
  have c1n10 := hc 1 (-1) 0
  have c111 := hc 1 1 1
  simp only [cubic] at c001 c010 c100 c011 c01n1 c101 c10n1 c110 c1n10 c111
  have r111 := hr 1 1 1
  have r211 := hr 2 1 1
  have r121 := hr 1 2 1
  have r112 := hr 1 1 2
  simp only [bracket] at r111 r211 r121 r112
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [p0, ca, cm, cp, cz]
    linear_combination hk
  · linear_combination q001
  · linear_combination q011-q001-q010
  · linear_combination q010
  · linear_combination q101-q001-q100
  · linear_combination q110-q010-q100
  · linear_combination q100
  · linear_combination c001
  · linear_combination (1 / 2 : ℂ) * (c011+c01n1)-c010
  · linear_combination (1 / 2 : ℂ) * (c011-c01n1)-c001
  · linear_combination c010
  · linear_combination (1 / 2 : ℂ) * (c101+c10n1)-c100
  · linear_combination c111-c011-c101-c110+c001+c010+c100
  · linear_combination (1 / 2 : ℂ) * (c110+c1n10)-c100
  · linear_combination (1 / 2 : ℂ) * (c101-c10n1)-c001
  · linear_combination (1 / 2 : ℂ) * (c110-c1n10)-c010
  · linear_combination c100
  · linear_combination (1 / 2 : ℂ) * r112-r111
  · linear_combination (1 / 2 : ℂ) * r121-r111
  · linear_combination (1 / 2 : ℂ) * r211-r111

set_option maxHeartbeats 10000000 in
theorem actual_matrix_equations (a b c l m n h : ℂ) (hk : h ^ 2 = 24)
    (HP : ∀ x y z w : ℂ, Matrix.permanent
      (Matrix.of fun i j => h + w * model a b c l m n h x y z i j) =
        24 * (h + w * (a*x+b*y+c*z)) ^ 4) :
    p0 a b c l m n h = 0 ∧
    p1 a b c l m n h = 0 ∧
    p2 a b c l m n h = 0 ∧
    p3 a b c l m n h = 0 ∧
    p4 a b c l m n h = 0 ∧
    p5 a b c l m n h = 0 ∧
    p6 a b c l m n h = 0 ∧
    p7 a b c l m n h = 0 ∧
    p8 a b c l m n h = 0 ∧
    p9 a b c l m n h = 0 ∧
    p10 a b c l m n h = 0 ∧
    p11 a b c l m n h = 0 ∧
    p12 a b c l m n h = 0 ∧
    p13 a b c l m n h = 0 ∧
    p14 a b c l m n h = 0 ∧
    p15 a b c l m n h = 0 ∧
    p16 a b c l m n h = 0 ∧
    p17 a b c l m n h = 0 ∧
    p18 a b c l m n h = 0 ∧
    p19 a b c l m n h = 0 := by
  apply extract_equations a b c l m n h hk
  intro x y z w
  have he := permanent_expansion a b c l m n h x y z w hk
  rw [HP x y z w] at he
  linear_combination -he

end PEqualNP.Outside.L_gct_231_aux.TopAllZeroBridge
