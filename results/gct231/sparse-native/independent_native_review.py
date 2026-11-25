"""Read-only independent review of frozen native source and all saved controls."""
from datetime import datetime, timezone
from pathlib import Path
import difflib
import hashlib
import json
import subprocess
import sympy as s

base = Path(__file__).resolve().parent
parent = base.parent
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
print('Start UTC', datetime.now(timezone.utc).isoformat(), flush=True)
prov = json.loads((base / 'provenance.json').read_text())
assert sha(base / 'provenance.json') == 'f107a8ea3d4b3499690a25dd5fed9c3b83cca2ce2fb3837992a64adf3c6a9542'
for name, expected in prov['files'].items():
    assert sha(base / name) == expected, name
original = json.loads((parent / 'provenance.json').read_text())
for name, expected in original['files'].items():
    assert sha(parent / name) == expected, name
print('All 10 native and 17 original frozen hashes match', flush=True)
assert (base / 'engine/gb.c').read_bytes() == (parent / 'qqfix/gb.c').read_bytes()
assert (base / 'engine/la_qq.c').read_bytes() == (parent / 'qqfix/la_qq.c').read_bytes()
upstream = (parent / 'msolve/src/neogb/convert.c').read_text()
old = '#pragma omp parallel for num_threads(st->nthrds) \\\n    private(i, j, k)\n    for (k = 0; k < np; ++k) {'
new = '/* Keep basis conversion serial: deg and constant flag have serial semantics. */\n    for (k = 0; k < np; ++k) {'
assert upstream.count(old) == 1
assert upstream.replace(old, new) == (base / 'engine/convert.c').read_text()
for src, dst, patch in [
    (parent / 'neogb_cli.c', base / 'neogb_cli_native.c', 'neogb_cli_native.patch'),
    (parent / 'run_neogb_qqfix.py', base / 'run_neogb_native.py', 'run_neogb_native.patch'),
    (parent / 'msolve/src/neogb/convert.c', base / 'engine/convert.c', 'openmp-conversion.patch'),
]:
    lines = (base / patch).read_text().splitlines(keepends=True)
    actual = list(difflib.unified_diff(src.read_text().splitlines(keepends=True),
                                     dst.read_text().splitlines(keepends=True)))
    assert actual[2:] == lines[2:], patch
print('Source deltas exactly match all three recorded patches', flush=True)
dyn = subprocess.check_output(['readelf', '-d', str(base / 'neogb_cli_native')], text=True)
assert '[libneogb_native.so]' in dyn and '[' + str(base) + ']' in dyn
libdyn = subprocess.check_output(['readelf', '-d', str(base / 'libneogb_native.so')], text=True)
assert 'libgomp.so' in libdyn and 'libgmp.so' in libdyn
cpu = json.loads((parent / 'native-cpu.json').read_text())
flags = next(item['data'] for item in cpu['lscpu'] if item['field'] == 'Flags:').split()
assert 'avx2' in flags and 'avx512f' in flags
macros = (parent / 'native-compiler-macros.log').read_text()
assert '#define __AVX2__ 1' in macros and '#define __AVX512F__ 1' in macros
print('Expected native runpath, GMP/OpenMP dependencies and CPU/compiler capabilities verified', flush=True)

metas = sorted(base.glob('sanity-*.result.json'))
metas += sorted((base / 'extra-controls').glob('*.result.json'))
metas += sorted((base / 'vector-controls').glob('*.result.json'))
assert len(metas) == 64
records = []
for path in metas:
    meta = json.loads(path.read_text())
    assert meta['status'] == 'COMPLETED' and meta['returncode'] == 0, path
    cmd = meta['command']
    assert Path(cmd[0]) == base / 'neogb_cli_native'
    infile, outfile = map(Path, cmd[1:3])
    assert meta['threads'] in (1, 2, 3) and int(cmd[4]) == meta['threads']
    assert meta['cpu_soft_seconds'] == meta['wall_limit_seconds'] * meta['threads'] + 2
    for key, file in [('binary_sha256', base / 'neogb_cli_native'),
                      ('library_sha256', base / 'libneogb_native.so'),
                      ('input_sha256', infile), ('output_sha256', outfile)]:
        assert meta[key] == sha(file), (path, key)
    data = list(map(int, infile.read_text().split()))
    n, m, characteristic, nt = data[:4]
    lengths = data[4:4 + m]
    pos = 4 + m
    xs = s.symbols('x:' + str(n))
    polys = []
    for length in lengths:
        expr = 0
        seen = set()
        for _ in range(length):
            a, b = data[pos:pos + 2]
            e = tuple(data[pos + 2:pos + 2 + n])
            pos += 2 + n
            assert e not in seen
            seen.add(e)
            expr += s.Rational(a, b) * s.prod(x ** power for x, power in zip(xs, e))
        polys.append(s.Poly(expr, *xs, domain=s.QQ).clear_denoms()[1].as_expr())
    assert pos == len(data) and sum(lengths) == nt
    out = json.loads(outfile.read_text())
    assert out['characteristic'] == characteristic and out['nvars'] == n
    assert sum(map(len, out['basis'])) == out['nterms']
    actual = [sum(s.Integer(c) * s.prod(x ** power for x, power in zip(xs, e))
                  for c, e in row) for row in out['basis']]
    kwargs = {'modulus': characteristic} if characteristic else {'domain': s.QQ}
    expected = s.groebner(polys, *xs, order='grevlex', **kwargs)
    normalize = lambda f: tuple(s.Poly(f, *xs, **kwargs).monic().terms())
    assert len(actual) == len(expected.polys)
    assert {normalize(f) for f in actual} == {normalize(f.as_expr()) for f in expected.polys}
    unit = list(expected) == [1]
    assert meta['unit_basis'] == unit and meta['basis_size'] == len(actual)
    print(path.relative_to(base), 'PASS', flush=True)
    records.append({'metadata': str(path.relative_to(base)), 'metadata_sha256': sha(path),
                    'characteristic': characteristic, 'threads': meta['threads'],
                    'basis_size': len(actual), 'unit': unit})
(base / 'independent-native-results.json').write_text(json.dumps(records, indent=2) + '\n')
print('All 64 saved controls independently match complete monic reduced Sympy bases', flush=True)
print('No solver rerun or compile performed; no claim of proof certificate or exhaustive concurrency audit', flush=True)
print('Finish UTC', datetime.now(timezone.utc).isoformat(), flush=True)
print('PASS', flush=True)
