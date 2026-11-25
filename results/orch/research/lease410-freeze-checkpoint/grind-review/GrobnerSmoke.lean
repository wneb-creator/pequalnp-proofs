import Mathlib.Basic.Complex.Basic
import Lean.Elab.Tactic.Grind

namespace PEqualNPGrindCapability

theorem nonlinear_unit (x y : ℂ) (h1 : x * y = 1) (h2 : x ^ 2 = 0) : False := by
  grobner (ringSteps := 10000) (ringMaxDegree := 8)

theorem nonlinear_disequality (x : ℂ) (h1 : x ^ 2 = 0) : x = 0 := by
  grobner (ringSteps := 10000) (ringMaxDegree := 8)

theorem integer_constant (x : ℂ) (h1 : 2 * x ^ 2 + 2 = 0) (h2 : 3 * x = 0) : False := by
  grobner (ringSteps := 10000) (ringMaxDegree := 8)

end PEqualNPGrindCapability
