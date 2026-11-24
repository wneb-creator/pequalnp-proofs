"""Independently evaluate a raw candidate, then check constant-free normalization.

Exit 0 means exact target and at most 21 gates after normalization, not Lean
acceptance. Exit 2 includes exact but oversized controls and malformed inputs.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path

EDGES=((0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
       (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9))
NORMALIZER_SHA='b807c1a580ce1fa49da51d859e6bc5d94bab2f9f0cd359c35cef35686f826529'

def require(ok,message):
    if not ok:raise ValueError(message)

def check_structure(obj):
    require(type(obj) is dict,'Candidate must be a JSON object')
    require(type(obj.get('inputs')) is int and obj['inputs']==11,'Exactly 11 inputs required')
    offset=obj.get('gate_wire_offset')
    require(type(offset) is int and offset in (11,13),'Wire offset must be 11 or 13')
    gates=obj.get('gates')
    require(type(gates) is list and len(gates)<=1000,'Invalid gate list')
    for i,g in enumerate(gates):
        require(type(g) is list and len(g)==3,'Every gate must have two operands')
        op,a,b=g
        require(type(op) is str and op in ('and','or'),'Only AND and OR are allowed')
        require(type(a) is int and type(b) is int and 0<=a<offset+i and 0<=b<offset+i,
                'Operands must refer to earlier wires')
    output=obj.get('output')
    require(type(output) is int and 0<=output<offset+len(gates),'Invalid output wire')
    return offset,gates,output

def scalar_check(obj):
    offset,gates,output=check_structure(obj)
    for mask in range(2048):
        values=[bool(mask&(1<<i)) for i in range(11)]
        if offset==13:values.extend([False,True])
        for op,a,b in gates:
            values.append((values[a] and values[b]) if op=='and' else (values[a] or values[b]))
        wanted=any((mask&(1<<u)) and (mask&(1<<v)) for u,v in EDGES)
        require(values[output]==wanted,f'Target mismatch at input {mask}')

def validate(source,normalizer):
    raw=source.read_bytes();obj=json.loads(raw)
    scalar_check(obj)
    offset,gates,output=check_structure(obj)
    if offset==11:
        lift=lambda w:w if w<11 else w+2
        gates=[[op,lift(a),lift(b)] for op,a,b in gates];output=lift(output)
    require(hashlib.sha256(normalizer.read_bytes()).hexdigest()==NORMALIZER_SHA,
            'Normalizer source hash mismatch')
    spec=importlib.util.spec_from_file_location('verified_normalizer',normalizer)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    result=module.normalize_circuit(gates,output)
    require('constant_output' not in result,'Normalization unexpectedly became constant')
    result.update(gate_wire_offset=11)
    scalar_check(result)
    require(result['size']==len(result['gates'])<=len(gates),'Normalization size mismatch')
    within=result['size']<=21
    result.update(gap='L-meta-1342',verified_inputs=2048,meets_posted_gate_limit=within,
                  requires_Lean_proof=True,source_sha256=hashlib.sha256(raw).hexdigest(),
                  validator_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  normalizer_sha256=NORMALIZER_SHA,
                  status='EXACT_AT_MOST_21' if within else 'EXACT_BUT_TOO_LARGE')
    return result

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('source',type=Path);p.add_argument('report',type=Path)
    p.add_argument('--normalizer',type=Path,default=Path(__file__).parent/'lean-setup/validate_sat_candidate.py')
    a=p.parse_args()
    try:
        require(not a.report.exists(),'Refusing to overwrite an existing report')
        result=validate(a.source,a.normalizer)
        a.report.write_text(json.dumps(result,indent=2)+'\n')
        print(result['status'],'size',result['size'],'verified_inputs',2048)
        raise SystemExit(0 if result['meets_posted_gate_limit'] else 2)
    except (ValueError,OSError,TypeError,KeyError,json.JSONDecodeError) as e:
        print('REJECTED:',str(e));raise SystemExit(2)
