"""Independent exact coefficient check for the two-block stratum argument."""
from itertools import permutations
import sympy as s

a, b, c, d, x, z, t = s.symbols('a b c d x z t')
matrix = s.Matrix([[a, x, 0, 0], [x, b, 0, 0],
                   [0, 0, c, z], [0, 0, z, d]])
permanent = sum(s.prod(1+t*matrix[i, permutation[i]] for i in range(4))
                for permutation in permutations(range(4)))
sa, sb = a+b+2*x, c+d+2*z
pa, pb = a*b+x*x, c*d+z*z
expected = 24+6*(sa+sb)*t+2*(pa+pb+sa*sb)*t**2
expected += (sa*pb+sb*pa)*t**3+pa*pb*t**4
assert s.expand(permanent-expected) == 0
alpha, beta = s.symbols('alpha beta')
diag0 = alpha*x+beta*z
diag1 = -2*x-diag0
block_permanent = s.Poly(s.expand(diag0*diag1+x*x), x, z)
assert block_permanent.coeff_monomial(z*z) == -beta*beta
assert s.expand(block_permanent.coeff_monomial(x*x)) == -alpha*alpha-2*alpha+1
print('PASS exact block-diagonal permanent expansion by all24 permutations.')
print('Coefficients:', [s.factor(s.Poly(permanent, t).nth(i)) for i in range(1, 5)])
print('Over the polynomial domain C[x,z], coefficient vanishing implies')
print('sb=-sa, pa+pb=sa^2, sa*(pb-pa)=0, pa*pb=0.')
print('The last equation gives pa=0 or pb=0, hence sa^3=0 and sa=sb=pa=pb=0.')
print('Then each block has no cross-parameter diagonal term: beta^2=0.')
print('Its remaining diagonal coefficient satisfies alpha^2+2alpha-1=0.')
print('Swapping the two vertices sends alpha to -2-alpha and exchanges the roots.')
print('Conditional stratum calculation only; no global chart exclusion is asserted.')
