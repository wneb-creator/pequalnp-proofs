Checked general all-D-zero pencil normalization, local research result for L-gct-231.

Given a symmetric pencil with first row (0,x,y,z), diagonal lower entries c0*x,c1*y,c2*z, arbitrary linear opposite-edge forms, and permanent(J+w*N)=24*(1+w*ell)^4, AllZeroGeneralNormalization.lean constructs h,l,m,n with h^2=24 and proves h*N is exactly TopAllZeroBridge.model with a=h*p,b=h*q,c=h*r. It also proves the full scaled permanent identity required by actual_model_impossible. A supplied scalar h0 with h0^2=24 is used only to select coherent binary signs.

Proof stages: four finite evaluations extract the first and fourth coefficients; each coordinate-plane restriction is a square; the previously checked sign-gluing and skew-reconstruction theorems give the canonical matrix; permanent_smul transports the identity. All stages are Lean checked, with no CAS assertion or remaining geometric callback.

Pinned Lean exit0,12.8165seconds,peakRSS2531733504bytes under4GiB/120seconds. Full stdout/stderr and run metadata are preserved. This source proves normalization only, not the normalized model obstruction or the complete gap statement. The posted-statement checker does not apply to this auxiliary file.
