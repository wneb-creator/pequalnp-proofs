import argparse
import hashlib
import json
import subprocess
import time
from pathlib import Path

from joint_correlated import generate,load_variants
from joint_decode import decode


def normalize(seed,ninputs):
    raw = seed['gates'] if isinstance(seed,dict) else seed
    gates = [['or' if op in (1,'or') else 'and',a,b] for op,a,b in raw]
    mapping = {i:i for i in range(ninputs)}
    pending = set(range(len(gates)))
    ordered = []
    while pending:
        choices = []
        for index in pending:
            op,a,b = gates[index]
            if a in mapping and b in mapping:
                a,b = sorted((mapping[a],mapping[b]))
                choices.append(((a,b,op == 'or'),index,[op,a,b]))
        assert choices
        _,index,gate = min(choices)
        mapping[ninputs+index] = ninputs+len(ordered)
        ordered.append(gate)
        pending.remove(index)
    assert mapping[ninputs+len(gates)-1] == ninputs+len(gates)-1
    return ordered


def fix(base,path,gates,extra_units):
    metadata = json.loads(base.with_suffix('.map.json').read_text())
    units = []
    assert len(gates) == metadata['gates']
    for (op,a,b),structure in zip(gates,metadata['structure']):
        units.extend((structure['left'][a],structure['right'][b],
                      structure['op'] if op == 'or' else -structure['op']))
    units.extend(extra_units)
    text = base.read_text().splitlines()
    assert text[0] == f'p cnf {metadata["nv"]} {metadata["clauses"]}'
    metadata['clauses'] += len(units)
    text[0] = f'p cnf {metadata["nv"]} {metadata["clauses"]}'
    text.extend(f'{literal} 0' for literal in units)
    assert not path.exists() and not path.with_suffix('.map.json').exists()
    path.write_text('\n'.join(text)+'\n')
    metadata['cnf_file'] = str(path.resolve())
    metadata['cnf_sha256'] = hashlib.sha256(path.read_bytes()).hexdigest()
    metadata['fixed_smoke_gates'] = gates
    metadata['fixed_smoke_units'] = extra_units
    path.with_suffix('.map.json').write_text(json.dumps(metadata)+'\n')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--variants',type=Path,nargs='+',required=True)
    parser.add_argument('--baseline',type=Path,required=True)
    parser.add_argument('--prefix',type=Path,required=True)
    parser.add_argument('--solver',type=Path,required=True)
    args = parser.parse_args()
    variants = load_variants(args.variants)
    baseline = json.loads(args.baseline.read_text())
    gates = normalize(baseline,variants[0]['data']['cut_inputs'])
    base = Path(str(args.prefix)+'-base.cnf')
    summary = generate(variants,len(gates),base)
    metadata = json.loads(base.with_suffix('.map.json').read_text())
    assert metadata['varying_cells']
    results = []
    def run(name,units,expected,branch=None):
        path = Path(str(args.prefix)+'-'+name+'.cnf')
        fix(base,path,gates,units)
        log = path.with_suffix('.solve.log')
        command = [str(args.solver),'-s','--time=2','--seed=1',str(path)]
        started = time.monotonic()
        with log.open('w') as stream:
            code = subprocess.run(command,stdout=stream,stderr=subprocess.STDOUT).returncode
        item = dict(name=name,expected=expected,exit_code=code,
                    wall_seconds=round(time.monotonic()-started,6),command=command)
        assert code == (10 if expected == 'SAT' else 20), item
        if code == 10:
            checked = decode(path.with_suffix('.map.json'),log,path.with_suffix('.verified.json'))
            if branch is not None:
                assert checked['selected_branch_index'] == branch
            item.update(selected_branch=checked['selected_branch_index'],
                        full_gate_count=checked['full_gate_count'],
                        checked_full_assignments=checked['checked_full_assignments'])
        results.append(item)
    run('free-selector',[],'SAT')
    for index,selector in enumerate(metadata['variant_selectors']):
        run(f'branch-{index}',[selector],'SAT',index)
        cell = metadata['varying_cells'][0]
        wrong = -cell['variable'] if cell['bits'][index] else cell['variable']
        run(f'branch-{index}-wrong-cut',[selector,wrong],'UNSAT')
    run('no-selector',[-s for s in metadata['variant_selectors']],'UNSAT')
    run('two-selectors',metadata['variant_selectors'][:2],'UNSAT')
    result = dict(encoding=summary,baseline=str(args.baseline.resolve()),results=results,
                  all_passed=True,scope='Fixed known baseline and selector/cut consistency smokes only; no target-budget search.')
    Path(str(args.prefix)+'-result.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(all_passed=True,smokes=len(results),variants=len(variants),
                          baseline_gates=len(gates),encoding=summary)),flush=True)


if __name__ == '__main__':
    main()
