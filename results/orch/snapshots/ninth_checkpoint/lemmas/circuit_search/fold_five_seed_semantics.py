"""Finite neutral folding of five-owner seeds using exact raw-input DNFs."""
import json
import runpy
from pathlib import Path

HERE = Path(__file__).resolve().parent
ALG = HERE.parent / 'algebra_strategy'
case = json.loads((ALG / 'five-owner-joint-packet.json').read_text())[0]
assembler = runpy.run_path(str(ALG / 'assemble_five_owner.py'))
assemble, compact = assembler['assemble_five'], assembler['compact_core']
n, raw = case['inputs'], case['raw_inputs']
inputs = [frozenset([1 << i]) for i in range(raw)]
inputs += [frozenset(1 << i for i in feature['raw_indices']) for feature in case['features']]

def normalize(terms):
    out = []
    for term in sorted(terms, key=lambda v: (v.bit_count(), v)):
        if not any(prior & term == prior for prior in out):
            out.append(term)
    return frozenset(out)

def fold(gates):
    terms, ren, made = inputs.copy(), list(range(n)), []
    cache = {signature: i for i, signature in enumerate(inputs)}
    for i, (op, a, b) in enumerate(gates):
        signature = normalize(terms[a] | terms[b] if op else
                              {u | v for u in terms[a] for v in terms[b]})
        terms.append(signature)
        if signature not in cache:
            cache[signature] = n + len(made)
            made.append([op, ren[a], ren[b]])
        ren.append(cache[signature])
    result, output, _ = compact(n, made, ren[-1])
    assert output == n + len(result) - 1
    return result, terms[-1]

improved = []
for index, seed in enumerate(json.loads((HERE / 'joint-five-seeds.json').read_text())):
    gates, signature = fold(seed['gates'])
    again, second = fold(gates)
    assert signature == second
    _, metadata = assemble(case, gates)
    old = seed['assembly']['core_gates'] + seed['assembly']['prefix_extra_cost']
    new = metadata['core_gates'] + metadata['prefix_extra_cost']
    if new < old:
        improved.append(dict(source_index=index, gates=gates, effective_before=old,
                             effective_after=new, assembly=metadata))
(HERE / 'joint-five-neutral-folds.json').write_text(json.dumps(improved))
print(dict(seeds=72, strictly_cheaper=len(improved),
           best_effective=min((x['effective_after'] for x in improved), default=None)))
