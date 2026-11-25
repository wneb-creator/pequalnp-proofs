"""Generate an uncompiled, original-name flat-table candidate for review."""
import hashlib
import json
from pathlib import Path
import re
import estimate_flat12203 as codec

repo = Path('/workspace/pequalnp-proofs')
original = codec.text
candidate = original
expected = set()
changed = []

def data_expression(chunks, variable):
    def tree(a, b):
        if b - a == 1:
            return hex(chunks[a])
        middle = (a + b)//2
        return f'(if {variable}<{middle} then {tree(a, middle)} else {tree(middle, b)})'
    return tree(0, len(chunks))

for row in codec.report['records']:
    if not row['compact']:
        continue
    name = row['data_name']
    fields = row['fields']
    word, _ = codec.data_words(name)
    decoded = [codec.decode(fields, word, row['raw'], i) for i in range(fields[0])]
    new_fields, chunks, _ = codec.flattened(fields, decoded, row['raw'])
    old_tuple = '(' + ','.join(map(str, fields)) + ',' + name + ')'
    new_tuple = '(' + ','.join(map(str, new_fields)) + ',' + name + ')'
    assert candidate.count(old_tuple) == 1, name
    tuple_owner = [key for key, declaration in codec.decls.items() if old_tuple in declaration]
    assert len(tuple_owner) == 1, (name, tuple_owner)
    expected.add(tuple_owner[0])
    candidate = candidate.replace(old_tuple, new_tuple, 1)
    old_decl = codec.decls[name]
    assert candidate.count(old_decl) == 1, name
    variable = re.search(r'\(([ij]) : Nat\)', old_decl)[1]
    new_decl = old_decl.split(':=', 1)[0] + ':= ' + data_expression(chunks, variable)
    candidate = candidate.replace(old_decl, new_decl, 1)
    expected.add(name)
    changed.append({'data_name': name, 'tuple_owner': tuple_owner[0],
        'old_fields': fields, 'new_fields': new_fields,
        'data_decl_growth_bytes': len(new_decl.encode()) - len(old_decl.encode()),
        'tuple_growth_bytes': len(new_tuple) - len(old_tuple),
        'decoded_sha256': row['decoded_sha256']})

def declarations(text):
    starts = list(re.finditer(r'(?m)^(?:private )?(?:def|theorem|lemma|abbrev|structure|inductive|set_option)\s+([^\s:(]+)', text))
    return {m[1]: text[m.start():starts[i+1].start() if i+1 < len(starts) else len(text)].strip()
            for i, m in enumerate(starts) if not m[0].startswith('set_option')}

after = declarations(candidate)
assert set(after) == set(codec.decls)
actual = {name for name in after if after[name] != codec.decls[name]}
assert actual == expected, (actual - expected, expected - actual)
assert all(not codec.decls[name].startswith(('theorem ', 'lemma ')) for name in actual)
attributed = (repo / 'results/orch/lemmas/Compact12203OriginalCandidate.lean').read_text()
insertion = original.index('\n') + 1
credit_length = len(attributed) - len(original)
credit = attributed[insertion:insertion + credit_length]
assert attributed == original[:insertion] + credit + original[insertion:]
credit = credit.replace('Original proof, batching, data, and credits are retained without modification.',
    'Original proofs and batching retained; packed tables expanded with identical decoded nodes and ordered hints.')
output = repo / 'results/orch/lemmas/Compact12203FlatOriginalNames.lean'
output.write_text(candidate[:insertion] + credit + candidate[insertion:])
report = {'status': 'UNCOMPILED candidate; independently audit and replay before claiming proof',
    'source': str(output), 'source_sha256': hashlib.sha256(output.read_bytes()).hexdigest(),
    'source_bytes': output.stat().st_size,
    'attributed_original_bytes': len(attributed.encode()),
    'growth_bytes': output.stat().st_size - len(attributed.encode()),
    'changed_packing_records': len(changed), 'changed_declarations': sorted(actual),
    'all_other_declarations_byte_identical': True,
    'all_theorems_byte_identical': True,
    'changes': changed}
(codec.BASE / 'flat12203-generation.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({k:v for k,v in report.items() if k not in ['changes', 'changed_declarations']}, indent=2))
