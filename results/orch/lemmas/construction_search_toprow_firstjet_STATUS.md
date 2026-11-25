# First-jet numerical exploration

This is a floating-point search, not a proof or an exhaustive count of algebraic solutions.

In the all-active, all-positive pair-sign top-row chart, the script eliminates the seven linear first-jet unknowns (six entries of a symmetric lower block and one power-form scalar) using a selected invertible seven-row minor. It solves the remaining three cubic compatibility equations and three quartic equations in six complex reconstruction parameters. An analytic implicit Jacobian agrees with finite differences to relative error6.8e-10.

The120-second run attempted803 initializations and recorded481 distinct numerical approximations under its clustering tolerance. This number includes near-singular approximations and is not a count of isolated algebraic points or components. None satisfied the higher-jet equations; the smallest recorded higher-jet residual norm was0.2558. Real and imaginary parameter parts were bounded to[-10,10], denominators and pivot conditioning were screened, and excluded or unbounded cases remain outside the search.

The fresh_geometry agent independently audited the model and one well-conditioned record. It reconstructed the lower block with separate formulas and expanded all35 quartic coefficients directly by permutations. For attempt410, the constant/first-jet coefficient residual norm was2.54e-13 and the higher-jet norm was14943.22695835, agreeing with the saved record. The full audit log is preserved. Of the481 recorded approximations,303 had reported Jacobian rank6 and selected-pivot condition number below10000; these remain numerical observations.

The search also approached the singular cyclic reconstruction C(t)=ell(t)J3/√2. Exact algebra reduces that special unrestricted extension branch to the two scalar equations q=16d²−72d+27=0 and g=64d³−432d²+108d+27=0. The identity (48d²−304d−45)q+(49−12d)g=108 excludes it. That observation has not been formalized here, and the target-specific rank-one case is separately covered by the team's star-plane argument.
