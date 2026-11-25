from datetime import datetime, timezone
from pathlib import Path
import hashlib
import json

base = Path('/tmp/oec/pequalnp-pilot-75/gct231')
engine = base / 'sparse-engine'
run = base / 'triangle-qq-trace-r1'
archive = Path('/workspace/pequalnp-proofs/results/gct231/neogb-primitive')
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
source = base / 'triangle_concept/triangle-twelve-equations.json'
assert digest(source) == '03a8aa61b2a83e2918457d922059fb481128cc02b3d1532c2cfcc11677ed0ce7'
prime_input = base / 'triangle-native-r1/triangle-p1009.in'
assert digest(prime_input) == '39b6adda8c99cc7cd7087165de43cb774000e3e16bd1e0aed577e05f83b85c74'
input_path = run / 'triangle-qq.in'
prime_lines = prime_input.read_text().splitlines()
qq_lines = input_path.read_text().splitlines()
assert prime_lines[0] == '12 26 1009 686'
assert qq_lines[0] == '12 26 0 686'
assert qq_lines[1:] == prime_lines[1:]
meta = json.loads((run / 'triangle-qq.provenance.json').read_text())
assert meta['characteristic'] == 0 and meta['source_sha256'] == digest(source)
assert meta['input_sha256'] == digest(input_path)
assert meta['dropped_modular_zero_terms'] == 0
print('All rational rows are byte-identical to the independently exact-reviewed input; only characteristic changed to zero.')
bindings = {
    'runner': engine / 'run_neogb_trace_primitive.py',
    'trace_source': engine / 'cert_trace_primitive.c',
    'generator': engine / 'make_cert_trace_primitive.py',
    'generated_qq_source': engine / 'certificate-trace-primitive/src/neogb/la_qq.c',
    'binary': engine / 'certificate-trace-primitive/neogb_cli_trace',
    'library': engine / 'certificate-trace-primitive/libneogb_trace.so',
}
expected = {
    'runner': '4623b7e6c2cd506a2043a7afc5a0905816d5a6976f64ab468b420c7a097869ba',
    'trace_source': '2ab5d0c46f1c9fee998122f58e959f38c72391d3f666af1bcfc279a7276c1676',
    'generator': '6bee4ca3cf45891420ee77bc182d109e8753f2b456aa5ecdb9bef99b9c77f0d1',
    'generated_qq_source': '9f9d0f95939606164ae8838a364fde08d28837b05a985d356863eec688483294',
    'binary': json.loads((archive / 'rowzero.run.json').read_text())['binary_sha256'],
}
for key, value in expected.items():
    assert digest(bindings[key]) == value, key
elf = (run / 'elf-dynamic.log').read_text()
assert 'Shared library: [libneogb_trace.so]' in elf
assert 'Library runpath: [' + str(bindings['binary'].parent) + ']' in elf
record = {
    'prepared_utc': datetime.now(timezone.utc).isoformat(),
    'source_sha256': digest(source),
    'input_sha256': digest(input_path),
    'bindings': {key: {'path': str(path), 'sha256': digest(path)}
                 for key, path in bindings.items()},
    'scope': 'Exact QQ trace research; no mathematical verdict without exact replay.',
}
(run / 'preflight.json').write_text(json.dumps(record, indent=2) + '\n')
print('Reviewed primitive engine source, binary, and RUNPATH checks PASS.')
print('PREFLIGHT PASS', digest(input_path))
