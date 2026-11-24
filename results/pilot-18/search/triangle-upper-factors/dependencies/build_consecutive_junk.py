"""Fresh shard encodings using an existence-preserving consecutive-junk normal form.

The added J18 unit is NOT claimed to follow logically from the input CNF.
Independent mathematical review is required before using these restrictions
to claim complete search. This program launches no solver and makes no requests.
"""
import argparse
import copy
import hashlib
import itertools
import json
from pathlib import Path

PARENT_SHA = '38d93ec59a86378a8434b232d19b2b53e8cbc3c715e81432ee94db59ca6ace08'
META_SHA = '5a430e86affc12584f964af39920201684505bafca4d34c1d30e6a10de3b9f51'
OPS = [2807, 3072, 3341, 3614]
JUNK = [2974, 3243, 3516, 3793]

def require(ok, message):
    if not ok:
        raise ValueError(message)

def digest(data):
    return hashlib.sha256(data).hexdigest()

def encode_json(value):
    return (json.dumps(value, indent=2) + '\n').encode()

def chain_clauses(meta, name):
    left, right = meta['lefts'], meta['rights']
    extra = []
    # The same chain topology works for the two different final operations.
    for g in (18, 19, 20):
        extra.append([right[g][13+g-1]])
        extra.extend([-v] for v in left[g][30:])
    if name == 'AAAA':
        leaves = [left[17][:30], right[17][:30], left[18][:30],
                  left[19][:30], left[20][:30]]
        strict = [False, False, True, True]
        extra.append([JUNK[2]])
    else:
        require(name == 'AAAO', 'Unknown chain case')
        # The final OR's other operand P is an arbitrary prefix wire.
        leaves = [left[17][:30], right[17][:30], left[18][:30], left[19][:30]]
        strict = [False, True, True]
        extra.append([-JUNK[2]])
    for earlier, later, is_strict in zip(leaves, leaves[1:], strict):
        for a in range(30):
            for b in range(30):
                if a > b or is_strict and a == b:
                    extra.append([-earlier[a], -later[b]])
    require(len(extra) == (1810 if name == 'AAAA' else 1375), 'Wrong chain delta')
    return extra

def generate(parent, output):
    raw = parent.read_bytes()
    meta_raw = parent.with_suffix('.json').read_bytes()
    require(digest(raw) == PARENT_SHA, 'Parent CNF hash mismatch')
    require(digest(meta_raw) == META_SHA, 'Parent metadata hash mismatch')
    meta = json.loads(meta_raw)
    require(meta['sha256'] == PARENT_SHA, 'Metadata CNF binding mismatch')
    require(meta['size'] == 21 and meta['first_junk'] == 17 and meta['second_junk'], 'Wrong shard')
    require(meta['original_DAG'] and meta['live'] and meta['last_output'], 'Missing parent normalization')
    require(meta['ops'][17:] == OPS and meta['junk'][17:] == JUNK, 'Wrong variable IDs')
    require([len(x) for x in meta['lefts'][17:]] == [30,31,32,33], 'Wrong left-port tables')
    require([len(x) for x in meta['rights'][17:]] == [30,31,32,33], 'Wrong right-port tables')
    header, body = raw.split(b'\n', 1)
    fields = header.split()
    require(fields[:2] == [b'p',b'cnf'], 'Wrong DIMACS header')
    variables, count = map(int, fields[2:])
    require((variables,count) == (11968,114566), 'Wrong parent dimensions')
    parsed = [list(map(int, line.split())) for line in body.splitlines()]
    require(len(parsed) == count, 'Parent clause count mismatch')
    require(all(c and c[-1] == 0 and all(0 < abs(v) <= variables for v in c[:-1]) for c in parsed), 'Malformed parent clause')
    clauses = {tuple(c[:-1]) for c in parsed}
    for c in [(JUNK[0],),(-JUNK[0],OPS[0]),(-JUNK[1],OPS[1]),tuple(JUNK[1:])]:
        require(c in clauses, 'Required original-shard clause missing')
    for i,j in itertools.combinations(range(4),2):
        require((OPS[i],OPS[j]) in clauses, 'Required three-AND clause missing')
    require(not output.exists(), 'Output directory already exists')
    program_sha = digest(Path(__file__).read_bytes())
    all_deltas = {'normalized': [[JUNK[1]]]}
    for name in ('AAAA','AAOA','AAAO'):
        op_units = [[v if op == 'A' else -v] for v,op in zip(OPS,name)]
        all_deltas[name] = [[JUNK[1]]] + op_units
    for name in ('AAAA','AAAO'):
        all_deltas[name+'-chain'] = all_deltas[name] + chain_clauses(meta,name)

    output.mkdir(parents=True,exist_ok=False)
    entries = {}
    for name, delta in all_deltas.items():
        addition = ''.join(' '.join(map(str,c))+' 0\n' for c in delta).encode()
        child = f'p cnf {variables} {count+len(delta)}\n'.encode()+body+addition
        child_meta = copy.deepcopy(meta)
        child_meta.update(
            sha256=digest(child), clauses=count+len(delta),
            consecutive_junk_parent_sha256=PARENT_SHA,
            consecutive_junk_parent_metadata_sha256=META_SHA,
            consecutive_junk_generator_sha256=program_sha,
            consecutive_junk=True, consecutive_junk_unit=JUNK[1],
            consecutive_junk_claimed_as_logical_consequence=False,
            consecutive_junk_justification='Existence normalization in S01-late-junk.md; independent S04 mathematical review pending.',
            consecutive_junk_added_clauses=delta,
            operation_case=None if name == 'normalized' else name.split('-')[0],
            fixed_chain=name.endswith('-chain'),
            research_status='GENERATED_ONLY_NO_SOLVER_VERDICT')
        if name.endswith('-chain'):
            child_meta['chain_justification'] = 'Minimal clean factor family; sort and repeat its smallest factor. Retains original FIRSTJ17 and at least two junk ANDs.'
            child_meta['chain_leaf_orders'] = 'a<=b<=c<d<e' if name=='AAAA-chain' else 'a<=b<c<d; P free'
        meta_bytes = encode_json(child_meta)
        with (output/(name+'.cnf')).open('xb') as f: f.write(child)
        with (output/(name+'.json')).open('xb') as f: f.write(meta_bytes)
        entries[name] = {'cnf_sha256':digest(child),'metadata_sha256':digest(meta_bytes),
                         'variables':variables,'clauses':count+len(delta),
                         'added_clauses':len(delta)}
    family = {
        'scope':'Existence-normalized original-shard research inputs; not a solver or Lean result.',
        'program_sha256':program_sha,'parent_sha256':PARENT_SHA,'parent_metadata_sha256':META_SHA,
        'mathematical_review':'AWAITING_INDEPENDENT_REVIEW',
        'added_J18_claimed_as_parent_logical_consequence':False,
        'normalized_parent':'normalized',
        'operation_partition':['AAAA','AAOA','AAAO'],
        'operation_partition_is_exact_for_normalized_parent':True,
        'alternative_chain_normalizations':['AAAA-chain','AAAO-chain'],
        'chain_variants_are_not_additional_disjoint_partition_cases':True,
        'files':entries}
    with (output/'family.json').open('xb') as f: f.write(encode_json(family))
    return family

if __name__ == '__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('parent',type=Path)
    parser.add_argument('output',type=Path)
    args=parser.parse_args()
    result=generate(args.parent,args.output)
    print(json.dumps({'generated':len(result['files']),'output':str(args.output),
                      'program_sha256':result['program_sha256'],
                      'scope':result['scope']}))
