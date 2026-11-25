from pathlib import Path
import hashlib
import json

repo = Path('/workspace/pequalnp-proofs')
scratch = Path('/tmp/oec/pequalnp-pilot-97')
target = repo / 'lean/PEqualNP/Outside/L_meta_2592.lean'
inputs = [
    scratch / 'FewNotBase.lean',
    scratch / 'PermutationSupport.lean',
    scratch / 'RowEmbeddingSupport.lean',
    repo / 'results/orch/lemmas/FewNotGeneric.lean',
    repo / 'results/orch/lemmas/GlobalSeventeen.lean',
]
prefix = 'PEqualNP.Outside.L_meta_2592.'
backup = scratch / 'L_meta_2592-before-seventeen.lean'
if not backup.exists():
    backup.write_bytes(target.read_bytes())
report = {'before_lines': len(backup.read_text().splitlines()), 'inputs': []}
parts = ['import PEqualNP.Defs', '', 'namespace PEqualNP.Outside.L_meta_2592', '']
for source in inputs:
    lines = source.read_text().splitlines()
    report['inputs'].append({'path': str(source), 'sha256': hashlib.sha256(source.read_bytes()).hexdigest(), 'lines': len(lines)})
    normalized = []
    for line in lines:
        if line.startswith('import '):
            continue
        if line.startswith('namespace ' + prefix):
            line = 'namespace ' + line[len('namespace ' + prefix):]
        elif line.startswith('end ' + prefix):
            line = 'end ' + line[len('end ' + prefix):]
        if source.name == 'GlobalSeventeen.lean':
            if line in ['set_option maxRecDepth 20000', 'set_option maxHeartbeats 0']:
                continue
            if line.startswith(('lemma ', 'def ')):
                normalized.extend(['set_option maxRecDepth 20000 in', 'set_option maxHeartbeats 0 in'])
        normalized.append(line)
    parts.extend(normalized)
    parts.append('')
parts.append('end PEqualNP.Outside.L_meta_2592')
text = '\n'.join(parts) + '\n'
assert text.count('import ') == 1
assert '_root_' not in text
assert chr(34) not in text
assert not any(line.startswith('theorem ') for line in parts)
assert not any('@[' in line and '@[simp]' not in line for line in parts)
target.write_text(text)
report['after_lines'] = len(text.splitlines())
report['sha256'] = hashlib.sha256(target.read_bytes()).hexdigest()
(scratch / 'global-seventeen-assembly.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
