#!/usr/bin/env python3
"""Portable hash verification, CNF restoration and retained-model validation only."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode=True
def digest(raw):return hashlib.sha256(raw).hexdigest()
def info(p):return {'bytes':p.stat().st_size,'sha256':digest(p.read_bytes())}
def require(ok,msg):
    if not ok:raise ValueError(msg)
def local(root,name):
    p=Path(name);require(not p.is_absolute() and '..' not in p.parts,'unsafe relative path')
    q=root/p;require(q.resolve().is_relative_to(root.resolve()),'path escape');return q
def module(path,name):
    spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m

def restore(root):
    manifest=json.loads((root/'MANIFEST.json').read_text())
    require(manifest['format']=='s06-sat-only-gadget-preservation-v1','format')
    for name,expected in manifest['payload'].items():
        p=local(root,name);require(p.is_file() and not p.is_symlink() and info(p)==expected,'payload mismatch '+name)
    recipes=json.loads((root/'CNF_RECIPES.json').read_text());restored=[];modules={}
    for entry in recipes['recipes']:
        generator=local(root,entry['generator'])
        require(info(generator)['sha256']==entry['generator_sha256'],'generator pin')
        if entry['gadget'] not in modules:modules[entry['gadget']]=module(generator,'archived_encoder'+str(entry['gadget']))
        encoder=modules[entry['gadget']];cnf,meta=encoder.build(entry['gates'])
        if entry['pin']!='none':
            circuit=encoder.circuit_controls()[0 if entry['pin']=='positive' else 1]
            units=encoder.pins(meta,circuit);cnf.clauses.extend(units)
            meta.update(pinned_circuit=circuit,pin_clause_count=len(units),scope='Fully pinned finite control only; not generic synthesis.')
        raw=cnf.raw();meta.update(clauses=len(cnf.clauses),cnf_sha256=digest(raw))
        metadata=(json.dumps(meta,indent=2,sort_keys=True)+'\n').encode()
        require(len(raw)==entry['bytes'] and digest(raw)==entry['sha256'],'CNF recipe')
        require(digest(metadata)==entry['metadata_sha256'],'metadata recipe')
        for alias in entry['aliases']:
            p=local(root,alias);require(p.with_suffix('.json').read_bytes()==metadata,'alias metadata')
            if p.exists():require(not p.is_symlink() and p.read_bytes()==raw,'existing CNF mismatch')
            else:
                with p.open('xb') as f:f.write(raw)
            restored.append(alias)
    require(set(restored)==set(manifest['omitted_cnfs']),'all CNF aliases restored')
    for name,expected in manifest['omitted_cnfs'].items():require(info(local(root,name))==expected,'CNF binding')
    require({str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}==set(manifest['payload'])|set(restored)|{'MANIFEST.json'},'unexpected file inventory')
    six=json.loads((root/'scratch/orch/S06/sat-only-gadget-handoff.json').read_text())
    for name,expected in six['files'].items():require(info(local(root,'scratch/'+name))==expected,'S06 handoff binding')
    five=json.loads((root/'scratch/orch/S05/kissat-sat-only-review-handoff.json').read_text())
    for entry in five['artifacts']:
        mapped=manifest['source_map'][entry['path']]['path']
        require(info(local(root,mapped))=={k:entry[k] for k in ['bytes','sha256']},'S05 handoff binding')
    for original,entry in manifest['source_map'].items():require(info(local(root,entry['path']))=={k:entry[k] for k in ['bytes','sha256']},'source map '+original)
    replays=[]
    for gadget,folder in [(7,'scratch/orch/S06/sat-only-gadget-controls-v1/positive12-gadget7'),(8,'scratch/orch/S06/sat-only-gadget-controls-v1/positive13-gadget8'),(7,'scratch/orch/S05/kissat-sat-only-review/real/g7-positive'),(8,'scratch/orch/S05/kissat-sat-only-review/real/g8-positive')]:
        p=root/folder;validator=module(root/f'scratch/orch/S0{5 if gadget==7 else 6}/validate_gadget{gadget}.py','archived_validator'+str(gadget))
        cnf=p/'instance.cnf';metadata=p/'instance.json'
        report=validator.validate(cnf.read_bytes(),metadata.read_bytes(),(p/'solver.stdout').read_bytes(),info(cnf)['sha256'],info(metadata)['sha256'])
        require(report==json.loads((p/'gadget.validated.json').read_text()),'retained full-model report differs')
        require(report['verified_inputs']==2**gadget and report['full11_verified_inputs']==2048 and report['full11_gate_count']==22 and report['meets_full21_gate_limit'] is False,'overlimit retained positive scope')
        replays.append({'path':folder,'gadget_inputs':2**gadget,'full_inputs':2048,'full_gate_count':22,'accepted_as21':False})
    return {'status':'PASS_PORTABLE_SAT_ONLY_PACKAGE','payloads':len(manifest['payload']),'source_map_bindings':len(manifest['source_map']),'S06_handoff_bindings':len(six['files']),'S05_handoff_bindings':len(five['artifacts']),'unique_cnf_recipes':len(recipes['recipes']),'restored_cnf_aliases':len(restored),'retained_positive_model_replays':replays,'solver_or_checker_launched':False}

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('root',type=Path);args=p.parse_args()
    print(json.dumps(restore(args.root.absolute()),indent=2,sort_keys=True))
