from pathlib import Path
import hashlib
import json
import re

source = Path('/workspace/pequalnp-proofs/results/orch/lemmas')
out = Path('/tmp/oec/pequalnp-pilot-87/rectangle-fixture')
out.mkdir(parents=True, exist_ok=True)
names = [
    'Live1024Count', 'State4ReadOnceForest', 'IndexedForest',
    'IntermediateCopyCut', 'CompressedWireCut', 'PrunedInterface',
    'SuccessorChecker', 'EntryGateChecker', 'EntryTableAdapters',
    'InitialRawState', 'PairColumnSemantics', 'CompressedIndexedForest',
    'PrunedStructural', 'PrunedBridgeResolve', 'PrunedMerge',
    'SharingReadOnce', 'PrunedDouble', 'PrunedSingleTransfer', 'PrunedSound',
    'RectangleRun', 'RectangleRunIndexed', 'RectangleFixture0Children',
    'RectangleFixture0Complete',
]
sha = lambda s: hashlib.sha256(s).hexdigest()
parts = ['import PEqualNP.Defs\n\n']
manifest = []
for name in names:
    path = source / (name + '.lean')
    original = path.read_bytes()
    body = original.decode()
    transforms = ['remove plain import lines']
    body = re.sub(r'^import [A-Za-z0-9_.]+\n', '', body, flags=re.M)
    if name == 'State4ReadOnceForest':
        begin = body.index('namespace State4Copy14\n')
        end = body.index('end State4Copy14\n', begin) + len('end State4Copy14\n')
        body = body[:begin] + body[end:]
        transforms.append('remove namespace State4Copy14 through its matching named end')
    body = body.strip() + '\n\n'
    manifest.append({'name': name, 'path': str(path), 'original_sha256': sha(original),
                     'original_bytes': len(original), 'body_sha256': sha(body.encode()),
                     'body_bytes': len(body.encode()), 'transforms': transforms})
    parts.append(body)
result = ''.join(parts).rstrip() + '\n'
target = out / 'RectangleFixture0Standalone.lean'
target.write_text(result)
report = {'target': str(target), 'sha256': sha(result.encode()),
          'bytes': len(result.encode()), 'lines': len(result.splitlines()),
          'pieces': manifest}
(out / 'assembly-manifest.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({k: v for k, v in report.items() if k != 'pieces'}))
