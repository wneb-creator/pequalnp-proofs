"""Independent exact check of the path-chart minor stratification."""
from itertools import combinations
import sympy as s

x, y, z = s.eye(3).columnspace()
a, b, c, d, e, f, g, h, j = s.symbols('a b c d e f g h j')
vectors = {
    (0, 1): x, (1, 2): y, (2, 3): z,
    (0, 2): s.Matrix([a, b, c]),
    (0, 3): s.Matrix([d, e, f]),
    (1, 3): s.Matrix([g, h, j]),
}
polynomials = []
for vertex in range(4):
    edges = [tuple(sorted((vertex, other))) for other in range(4)
             if vertex != other]
    polynomials.append(s.det(s.Matrix.hstack(*(vectors[edge] for edge in edges))))
for triangle in combinations(range(4), 3):
    polynomials.append(s.det(s.Matrix.hstack(
        *(vectors[edge] for edge in combinations(triangle, 2)))))
variables = (a, c, g, j, d, f, b, h, e)
basis = s.groebner(polynomials, *variables, order='lex')
expected = [a, c, g, j, b*d, b*f, h*d, h*f]
assert all(basis.reduce(poly)[1] == 0 for poly in expected)
reverse = s.groebner(expected, *variables, order='lex')
assert all(reverse.reduce(poly)[1] == 0 for poly in polynomials)
print('Raw eight star/triangle minors:', polynomials)
print('Reduced lex basis:', list(basis))
print('PASS ideal equality over QQ. Over any field, the displayed explicit')
print('minors give the same equations: a=c=g=j=0 and bd=bf=hd=hf=0.')
print('Consequently either d=f=0, or b=h=0.')
print('This is a conditional minor-stratification calculation, not a proof')
print('that the star/triangle charts have no permanent-constant planes.')
