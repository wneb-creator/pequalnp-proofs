import PEqualNP.Defs

set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

namespace PEqualNP.Outside.L_gct_231.trace

theorem rowzero_even_grind_medium (r s t u : ℂ)
    (h10 : (((2) + (r ^ 2)) : ℂ) = 0)
    (h0 : ((((-(t * r)) + (t ^ 2 * r)) + ((2 * s * t) + ((-2 * s * t * r) + (-(s ^ 3 * r))))) : ℂ) = 0)
    (h1 : (((((-(u * r)) + (2 * t)) + ((2 * t * r) + ((2 * t * u * r) + (2 * s * u)))) + (((-2 * s * u * r) + ((2 * s * t * r) + (s * t ^ 2 * r))) + ((-(s ^ 2 * r)) + ((-2 * s ^ 2 * t) + (-2 * s ^ 2 * t * r))))) : ℂ) = 0)
    (h2 : (((((r) + (2 * t * r)) + ((-2 * t * u) + ((2 * t * u * r) + (2 * t ^ 2 * r)))) + (((t ^ 3 * r) + ((2 * s) + (2 * s * r))) + ((-2 * s * t ^ 2) + ((-2 * s * t ^ 2 * r) + (3 * s ^ 2 * u * r))))) : ℂ) = 0)
    (h3 : (((((2 * u) + (2 * u * r)) + ((u ^ 2 * r) + ((s * r) + (2 * s * u * r)))) + (((-2 * s * t) + ((2 * s * t * r) + (2 * s * t * u * r))) + ((-2 * s ^ 2 * u) + ((-2 * s ^ 2 * u * r) + (-(s ^ 2 * t * r)))))) : ℂ) = 0)
    (h4 : (((((2) + ((-2 * r) + (2 * u * r))) + (((-2 * u ^ 2) + (2 * u ^ 2 * r)) + ((2 * t * u * r) + (-2 * t ^ 2)))) + ((((2 * t ^ 2 * r) + (2 * t ^ 2 * u * r)) + ((-2 * s * r) + (2 * s * u * r))) + (((2 * s * t * r) + (-2 * s * t ^ 2 * r)) + ((-2 * s ^ 2) + (2 * s ^ 2 * r))))) : ℂ) = 0)
    (h5 : (((((r) + (-2 * u)) + ((-2 * u * r) + ((-2 * t * r) + (2 * t ^ 2 * r)))) + (((2 * t ^ 2 * u) + ((2 * t ^ 2 * u * r) + (-(t ^ 3 * r)))) + ((-3 * s * u ^ 2 * r) + ((-2 * s * t) + (2 * s * t * r))))) : ℂ) = 0)
    (h6 : ((((r) + (-2 * s * u)) + ((2 * s * u * r) + ((s * u ^ 2 * r) + (-(s ^ 2 * u * r))))) : ℂ) = 0)
    (h7 : (((((-(u * r)) + (-2 * t * u)) + ((2 * t * u * r) + ((t * u ^ 2 * r) + (-2 * s)))) + (((-2 * s * r) + ((2 * s * u * r) + (2 * s * u ^ 2))) + ((2 * s * u ^ 2 * r) + ((-2 * s * t * u * r) + (s ^ 2 * r))))) : ℂ) = 0)
    (h8 : (((((-(u ^ 2 * r)) + (-2 * t)) + ((-2 * t * r) + ((2 * t * u * r) + (2 * t * u ^ 2)))) + (((2 * t * u ^ 2 * r) + ((-(t ^ 2 * u * r)) + (s * r))) + ((2 * s * u) + ((-2 * s * u * r) + (2 * s * t * r))))) : ℂ) = 0)
    (h9 : ((((u ^ 3 * r) + (t * r)) + ((2 * t * u) + ((-2 * t * u * r) + (t ^ 2 * r)))) : ℂ) = 0)
    : False := by
  grind (ringSteps := 100000) (ringMaxDegree := 8) (ematch := 0) (splits := 0) -linarith -lia

end PEqualNP.Outside.L_gct_231.trace

#print axioms PEqualNP.Outside.L_gct_231.trace.rowzero_even_grind_medium
