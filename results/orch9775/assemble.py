from pathlib import Path
import hashlib
import json
import re

repo = Path(__file__).resolve().parents[2]
root = repo / 'results/orch9775'
lemmas = root / 'lemmas'
private = {55, 95, 103, 119, 123, 181, 229, 245, 661, 2693, 4245, 4309, 5190}
text = (lemmas / 'PrivateProjection.lean').read_text()
blocks = list(re.finditer(r'(?m)^set_option maxHeartbeats 0 in\nset_option maxRecDepth 100000 in\ntheorem projection(\d+)', text))
end = text.rindex('\nend PEqualNP.Outside.L_meta_9775.UpstreamCore')
selected = [text[:blocks[0].start()]]
found = set()
for i, block in enumerate(blocks):
    number = int(block.group(1))
    if number in private:
        stop = blocks[i + 1].start() if i + 1 < len(blocks) else end
        selected.append(text[block.start():stop])
        found.add(number)
assert found == private
selected.append(text[end:])
(lemmas / 'PrivateProjectionSelected.lean').write_text(''.join(selected))

modules = [
    'UpstreamDagTools', 'UpstreamGraph', 'WeightClassification',
    'GraphSymmetry', 'RelabelSurplus', 'CompactFramework',
    'WeakCompactFramework', 'PairedExactFramework', 'CompactPacking',
    'PrivateProjectionSelected', 'Projection63', 'ResidualCodeExclusions',
    'ResidualShape4293', 'Public4293', 'Residual4293',
]
sources = [lemmas / (name + '.lean') for name in modules]
strong = [11, 47, 164, 177, 197, 266, 298, 400, 416, 432, 525, 645,
          1034, 1038, 1216, 1220, 1290, 2087]
sources += [root / 'search/compact-final' / f'P{n}.lean' for n in strong]
sources += [root / 'search/compact-final' / f'W{n}.lean' for n in [127, 1290, 4757]]
sources.append(lemmas / 'CompleteRefutationSlim.lean')

combined = ['import PEqualNP.Defs\n\n']
manifest = []
for path in sources:
    raw = path.read_text()
    body = ''.join(line for line in raw.splitlines(keepends=True)
                   if not line.startswith('import ')).strip()
    assert not re.search(r'\bimport\b', body), path
    combined.append(body + '\n\n')
    manifest.append({'path': str(path.relative_to(repo)),
                     'sha256': hashlib.sha256(raw.encode()).hexdigest(),
                     'bytes': len(raw.encode())})
output = ''.join(combined).rstrip() + '\n'
assert len(output.encode()) <= 512 * 1024, len(output.encode())
assert '_root_' not in output
assert '"' not in output
assert not re.search(r'\b(sorry|axiom|native_decide|unsafe|initialize)\b', output)
target = repo / 'lean/PEqualNP/Outside/L_meta_9775.lean'
target.write_text(output)
(root / 'standalone-assembly.json').write_text(json.dumps({
    'target': str(target.relative_to(repo)),
    'sha256': hashlib.sha256(output.encode()).hexdigest(),
    'bytes': len(output.encode()), 'lines': len(output.splitlines()),
    'sources': manifest,
}, indent=2) + '\n')
print(f'Assembled {len(output.encode())} bytes, {len(output.splitlines())} lines.')
