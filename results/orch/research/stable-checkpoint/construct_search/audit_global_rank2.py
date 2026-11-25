from pathlib import Path
import sympy as S
import json, collections, resource, time, hashlib

resource.setrlimit(resource.RLIMIT_AS, (384 * 2**20, 384 * 2**20))
resource.setrlimit(resource.RLIMIT_CPU, (150, 155))
base = Path('/tmp/oec/pequalnp-pilot-78/construct_search')
path = base / 'net_normal_form/global-rank2-charts.json'
data = json.loads(path.read_text())
results = []
start = time.monotonic()
for chart in data['charts']:
    v = S.symbols(' '.join(chart['variables']))
    local = dict(zip(chart['variables'], v))
    matrices = [S.zeros(4) for _ in range(3)]
    for (i, j), entries in zip(data['coordinate_order'], chart['basis_coefficients']):
        for matrix, entry in zip(matrices, entries):
            matrix[i, j] = matrix[j, i] = S.sympify(entry, locals=local)
    A, B, H = matrices
    assert list(A.diagonal()) == [1, 0, v[0], v[1]]
    assert list(B.diagonal()) == [0, 1, v[2], v[3]]
    assert list(H.diagonal()) == [0, 0, 0, 0]
    i, j = chart['pivot_edge']
    assert (A[i, j], B[i, j], H[i, j]) == (0, 0, 1)
    assert all(S.expand(sum(M)) == 0 for M in matrices)
    coordinates = S.Matrix([M[i, j] for M in matrices for i, j in data['coordinate_order']])
    assert coordinates.jacobian(v).rank() == 16
    poly = collections.defaultdict(lambda: S.Integer(0))
    for mask in range(1, 16):
        cols = [j for j in range(4) if mask >> j & 1]
        term = {(0, 0, 0): S.Integer((-1) ** (4 - len(cols)))}
        for i in range(4):
            co = [S.Integer(len(cols))] + [S.expand(sum(M[i, j] for j in cols)) for M in matrices]
            nxt = collections.defaultdict(lambda: S.Integer(0))
            for exp, val in term.items():
                nxt[exp] += val * co[0]
                for r in range(3):
                    ee = list(exp)
                    ee[r] += 1
                    nxt[tuple(ee)] += val * co[r + 1]
            term = nxt
        for exp, val in term.items():
            poly[exp] += val
    assert S.expand(poly[(0, 0, 0)] - 24) == 0
    for exp in [(1, 0, 0), (0, 1, 0), (0, 0, 1)]:
        assert S.expand(poly[exp]) == 0
    exponents = set()
    for eq in chart['equations']:
        exp = tuple(eq['parameter_exponents'])
        assert exp not in exponents
        exponents.add(exp)
        actual = S.Poly(S.expand(poly[exp]) * S.Rational(eq['scale_from_permanent_coefficient']), *v)
        supplied = S.Poly(S.sympify(eq['polynomial'].replace('^', '**'), locals=local), *v)
        assert actual == supplied, (chart['name'], exp)
        sparse = {tuple(e): S.Integer(c) for c, e in eq['terms']}
        assert supplied.as_dict() == sparse, (chart['name'], exp, 'sparse')
    expected = {(a, b, c) for a in range(5) for b in range(5-a) for c in range(5-a-b) if 2 <= a+b+c <= 4}
    assert exponents == expected
    record = {'name': chart['name'], 'coefficients': len(exponents), 'affine_coordinate_rank': 16, 'verdict': 'PASS'}
    results.append(record)
    print(json.dumps(record), flush=True)
record = {'verdict': 'PASS independent exact symbolic Ryser audit', 'source_sha256': hashlib.sha256(path.read_bytes()).hexdigest(), 'charts': results, 'seconds': time.monotonic()-start, 'scope': 'Complete normalized diagonal-rank-two three-flat chart equations and affine parameterizations; no feasibility conclusion'}
(base/'global-rank2-independent-audit.json').write_text(json.dumps(record, indent=2)+'\n')
print(json.dumps(record), flush=True)
