from pathlib import Path
import datetime
import hashlib
import json
import re

BASE = Path('/tmp/oec/pequalnp-pilot-81')
OUT = Path('/workspace/pequalnp-proofs/results/orch/lemmas')
DECL = re.compile(r"^(?:@\[[^\n]*\]\s*)?(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*(?:def|abbrev|lemma|theorem|structure|inductive|instance)\s+([A-Za-z_][A-Za-z0-9_'.]*)(?=\s|\(|\{|:|=|$)")
CONTEXT = re.compile(r'^(?:import|namespace|section|end|variable|open|attribute|set_option)\b|^noncomputable section\b')

def mask_comments(source):
    result = []
    i = 0
    depth = 0
    while i < len(source):
        if source.startswith('/-', i):
            depth += 1
            result.extend('  ')
            i += 2
        elif depth and source.startswith('-/', i):
            depth -= 1
            result.extend('  ')
            i += 2
        elif depth:
            result.append('\n' if source[i] == '\n' else ' ')
            i += 1
        elif source.startswith('--', i):
            j = source.find('\n', i)
            j = len(source) if j < 0 else j
            result.extend(' ' * (j-i))
            i = j
        else:
            result.append(source[i])
            i += 1
    assert depth == 0
    return ''.join(result)

def blocks_for(source):
    lines = source.splitlines(keepends=True)
    masked = mask_comments(source).splitlines(keepends=True)
    commands = []
    for i, line in enumerate(masked):
        match = DECL.match(line)
        if match:
            commands.append((i, match.group(1)))
        elif CONTEXT.match(line):
            commands.append((i, None))
    commands.append((len(lines), None))
    blocks = {}
    for (i, name), (j, _) in zip(commands, commands[1:]):
        if name:
            assert name not in blocks, name
            blocks[name] = (i, j)
    return lines, masked, blocks

def remove_blocks(source, names):
    lines, masked, blocks = blocks_for(source)
    excluded = set()
    for name in names:
        i, j = blocks[name]
        excluded.update(range(i, j))
        k = i-1
        while k >= 0 and re.match(r'^set_option\b.*\bin\s*$', masked[k]):
            excluded.add(k)
            k -= 1
    return ''.join(line for i, line in enumerate(lines) if i not in excluded)

source = (OUT/'algebraic-p9-mixed.lean').read_text()
lines, masked, blocks = blocks_for(source)
needed = set(re.findall(r'NEEDED PEqualNP\.Outside\.L_meta_6659_aux\.([^\s]+)', (BASE/'m9-dependency-audit.stdout').read_text()))
keep = {name for name in blocks if any(n == name or n.startswith(name+'.') for n in needed)}
initial = set(keep)
while True:
    new = set(keep)
    for name in keep:
        i, j = blocks[name]
        for token in re.findall(r"[A-Za-z_][A-Za-z0-9_']*", ''.join(masked[i:j])):
            if token in blocks:
                new.add(token)
    if new == keep:
        break
    keep = new
removed = set(blocks)-keep
pruned = remove_blocks(source, removed).replace('PEqualNP.Outside.L_meta_1479.MixedNine', 'PEqualNP.Outside.L_meta_1479.MixedNinePruned')
(OUT/'algebraic-p9-mixed-pruned.lean').write_text(pruned)

finite = set()
for filename in ['constructive-mixed9-finite.lean', 'formalization-cap-seven-complete.lean']:
    finite.update(blocks_for((OUT/filename).read_text())[2])
finite_here = finite & set(blocks_for(pruned)[2])
cached = remove_blocks(pruned, finite_here)
cached = cached.replace('import PEqualNP.Defs', 'import PNPMixed9Finite\nimport PNPCapSevenBridge', 1)
cached = cached.replace('PEqualNP.Outside.L_meta_1479.MixedNinePruned', 'PEqualNP.Outside.L_meta_6659_aux')
(OUT/'algebraic-p9-mixed-pruned-cache.lean').write_text(cached)

record = {
    'created_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'original_source': str(OUT/'algebraic-p9-mixed.lean'),
    'original_sha256': hashlib.sha256(source.encode()).hexdigest(),
    'pruned_source': str(OUT/'algebraic-p9-mixed-pruned.lean'),
    'pruned_sha256': hashlib.sha256(pruned.encode()).hexdigest(),
    'original_bytes': len(source.encode()), 'pruned_bytes': len(pruned.encode()),
    'pruned_lines': len(pruned.splitlines()), 'declarations_total': len(blocks),
    'dependency_retained': len(initial), 'syntactically_added': sorted(keep-initial),
    'removed_declarations': sorted(removed), 'retained_declarations': sorted(keep),
    'cached_source': str(OUT/'algebraic-p9-mixed-pruned-cache.lean'),
    'cached_sha256': hashlib.sha256(cached.encode()).hexdigest(),
    'cached_bytes': len(cached.encode()), 'imported_finite_declarations': sorted(finite_here),
    'scope': 'Dependency-guided removal of unused declaration blocks with conservative syntactic-reference closure. Original source unchanged; pruned sources require checking.'
}
(OUT/'algebraic-p9-mixed-pruning.json').write_text(json.dumps(record, indent=2)+'\n')
(BASE/'m9-dependency-pruning-blocks.json').write_text(json.dumps({'blocks': blocks, 'retained': sorted(keep), 'needed': sorted(needed)}, indent=2)+'\n')
print(json.dumps({key: record[key] for key in ['pruned_sha256', 'pruned_bytes', 'pruned_lines', 'cached_bytes', 'dependency_retained', 'syntactically_added']}))
