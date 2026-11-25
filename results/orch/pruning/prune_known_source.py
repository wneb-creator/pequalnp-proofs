"""Source-only, reversible pruning candidate. Never invokes Lean or edits main."""
import ast
import hashlib
import json
import re
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path('/workspace/pequalnp-proofs')
HERE = Path(__file__).resolve().parent
SCRATCH = Path('/tmp/oec/pequalnp-pilot-67/source-pruning')
SCRATCH.mkdir(exist_ok=True)
SOURCE = ROOT / 'lean/PEqualNP/Outside/L_meta_670.lean'
source_bytes = SOURCE.read_bytes()
source = source_bytes.decode()
assert hashlib.sha256(source_bytes).hexdigest() == '42bee598c028c21d1eeebcb40ff8435ce53b4bf5256c806ce0304c5721d581b6'
text = source
operations = []
iterations = []
helper_names = json.loads((SCRATCH.parent / 'optimizer/dependency-manifest.json').read_text())['removed']
empty_candidates = SCRATCH / 'empty-candidates.json'
empty_candidates.write_text('[]\n')
head = re.compile(r'^(?:(?:private|protected|noncomputable)\s+)*(?:def|theorem|lemma|abbrev|inductive|structure)\s+([^\s(:{]+)')


def declarations(s):
    lines = s.splitlines(keepends=True)
    offsets = [0]
    for line in lines:
        offsets.append(offsets[-1] + len(line))
    starts = []
    for i, line in enumerate(lines):
        m = head.match(line)
        if m:
            a = i
            while a > 0 and re.fullmatch(r'set_option \w+ \d+ in\n', lines[a - 1]):
                a -= 1
            starts.append((a, i, m[1]))
    result = {}
    for j, (start, line, name) in enumerate(starts):
        end = starts[j + 1][0] if j + 1 < len(starts) else len(lines)
        assert name not in result, name
        result[name] = {
            'start': offsets[start], 'end': offsets[end], 'line': line + 1,
            'text': s[offsets[start]:offsets[end]], 'first': lines[line].rstrip('\n'),
        }
    return result


def edit(position, old, new, reason):
    global text
    assert text[position:position + len(old)] == old
    operations.append({'offset_characters': position, 'old': old, 'new': new, 'reason': reason})
    text = text[:position] + new + text[position + len(old):]


def erase_decls(names, reason):
    ds = declarations(text)
    removals = [(ds[name]['start'], name, ds[name]['text']) for name in names]
    for pos, name, body in sorted(removals, reverse=True):
        assert not re.search(r'^(namespace|end |import )', body, re.M), name
        assert '/-' not in body and '--' not in body, name
        edit(pos, body, '', reason + ': ' + name)


def replace_names(mapping, reason):
    if not mapping:
        return
    pattern = re.compile(r'(?<![\w.])(' + '|'.join(re.escape(k) for k in mapping) + r')(?![\w.])')
    matches = list(pattern.finditer(text))
    for m in reversed(matches):
        edit(m.start(), m[0], mapping[m[0]], reason)


def census(iteration):
    current = SCRATCH / f'stage-{iteration}.lean'
    report_path = SCRATCH / f'stage-{iteration}-census.json'
    current.write_text(text)
    with (SCRATCH / f'stage-{iteration}-census.stdout').open('w') as out, (SCRATCH / f'stage-{iteration}-census.stderr').open('w') as err:
        result = subprocess.run([
            sys.executable, str(ROOT / 'results/orch/known_usage_census.py'),
            str(current), str(empty_candidates), str(report_path)
        ], cwd=ROOT, stdout=out, stderr=err)
    assert result.returncode == 0, (iteration, result.returncode)
    return json.loads(report_path.read_text())


# This deletion set was independently agreed by two earlier source analyses.
erase_decls(helper_names, 'Previously independently audited unused helper')
for name in helper_names:
    assert not re.search(r'(?<![\w.])' + re.escape(name) + r'(?![\w.])', text), name

report = census(0)
for iteration in range(1, 20):
    if not report['unused_entries']:
        break
    ds = declarations(text)
    unused = {}
    for entry in report['unused_entries']:
        unused.setdefault(entry['owner'], set()).add(entry['index'])
    empty = {}
    carry_edits = []
    for name, indexes in unused.items():
        d = ds[name]
        m = re.fullmatch(r'(noncomputable def ' + re.escape(name) + r' := extendKnown )(\[\]|known\d+) (\d+) (\[.*\])', d['first'])
        assert m, name
        entries = ast.literal_eval(m[4])
        kept = [entry for i, entry in enumerate(entries) if i not in indexes]
        if not kept:
            assert m[2] != '[]'
            empty[name] = m[2]
        else:
            new_literal = '[' + ','.join('(' + str(q) + ',[' + ','.join(map(str, swaps)) + '])' for q, swaps in kept) + ']'
            new_first = m[1] + m[2] + ' ' + m[3] + ' ' + new_literal
            pos = text.index(d['first'], d['start'], d['end'])
            carry_edits.append((pos, d['first'], new_first, name))
    for pos, old, new, name in sorted(carry_edits, reverse=True):
        edit(pos, old, new, f'Iteration {iteration}: remove numerically unqueried carry entries from {name}')
    # Empty groups retain no queried bound. Their lower bound is needed only to
    # establish those carries; prove this source fact before removing the group.
    ds = declarations(text)
    remove = []
    mapping = {}
    for name, predecessor in empty.items():
        number = name.removeprefix('known')
        low, valid = 'low' + number, 'valid' + number
        assert low in ds and valid in ds
        for other, decl in ds.items():
            if other not in (low, valid):
                assert not re.search(r'(?<![\w.])' + low + r'(?![\w.])', decl['text']), (low, other)
        resolved = predecessor
        while resolved in empty:
            resolved = empty[resolved]
        mapping[name] = resolved
        mapping[valid] = 'valid' + resolved.removeprefix('known')
        remove += [low, name, valid]
    erase_decls(remove, f'Iteration {iteration}: empty unqueried carry group')
    replace_names(mapping, f'Iteration {iteration}: bypass removed carry/valid chain node')
    for name in remove:
        assert not re.search(r'(?<![\w.])' + re.escape(name) + r'(?![\w.])', text), name
    iterations.append({
        'iteration': iteration, 'before_counts': report['counts'],
        'removed_carry_entries': report['unused_entries'],
        'empty_groups': empty, 'bypass_mapping': mapping,
        'removed_declarations': remove,
    })
    report = census(iteration)
else:
    raise AssertionError('Pruning did not converge in 19 iterations')

assert not report['unused_entries']
restored = text
for operation in reversed(operations):
    pos, old, new = operation['offset_characters'], operation['old'], operation['new']
    assert restored[pos:pos + len(new)] == new
    restored = restored[:pos] + old + restored[pos + len(new):]
assert restored == source
marker = 'theorem PEqualNP.Outside.L_meta_670 :'
assert source[source.index(marker):] == text[text.index(marker):]
assert source.split('namespace ', 1)[0] == text.split('namespace ', 1)[0]
assert SOURCE.read_bytes() == source_bytes
destination = HERE / 'L_meta_670_pruned.lean'
destination.write_text(text)
summary = {
    'status': 'SOURCE-ONLY CANDIDATE; FULL BUILD AND CHECKER UNVALIDATED',
    'utc': datetime.now(timezone.utc).isoformat(),
    'source': str(SOURCE), 'source_sha256': hashlib.sha256(source_bytes).hexdigest(),
    'candidate': str(destination), 'candidate_sha256': hashlib.sha256(text.encode()).hexdigest(),
    'source_bytes': len(source_bytes), 'candidate_bytes': len(text.encode()),
    'source_lines': len(source.splitlines()), 'candidate_lines': len(text.splitlines()),
    'unused_helpers_removed': helper_names,
    'iterations': iterations, 'final_counts': report['counts'],
    'numeric_census_is_not_kernel_validation': True,
    'reversible_operations_count': len(operations),
    'final_theorem_and_attribution_unchanged': True,
    'main_source_untouched': True,
}
(HERE / 'manifest.json').write_text(json.dumps({**summary, 'reversible_operations': operations}, indent=2) + '\n')
(HERE / 'final-query-census.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({k: v for k, v in summary.items() if k != 'iterations'}, indent=2))
for it in iterations:
    print('Iteration', it['iteration'], 'removed entries', len(it['removed_carry_entries']), 'empty groups', it['empty_groups'])
