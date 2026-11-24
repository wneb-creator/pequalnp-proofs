#!/usr/bin/env python3
"""Verify an extracted gadget8 package and restore CNFs without running a solver."""
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
def under(root,name):
    p=Path(name)
    require(not p.is_absolute() and '..' not in p.parts,'unsafe relative path')
    q=root/p
    require(q.resolve().is_relative_to(root.resolve()),'path escapes archive')
    return q

def restore(root):
    manifest=json.loads((root/'MANIFEST.json').read_text())
    require(manifest['format']=='s06-gadget8-preservation-v1','archive format')
    payload=manifest['payload']
    for name,expected in payload.items():
        p=under(root,name)
        require(p.is_file() and not p.is_symlink() and info(p)==expected,'payload mismatch '+name)
    recipes=json.loads((root/'CNF_RECIPES.json').read_text())
    source=under(root,recipes['generator'])
    require(info(source)['sha256']==recipes['generator_sha256'],'generator pin')
    spec=importlib.util.spec_from_file_location('archived_gadget8_encoder',source)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    positive,bad=module.circuit_controls()
    restored=[]
    for entry in recipes['recipes']:
        cnf,meta=module.build(entry['gates'])
        circuit={'none':None,'positive13':positive,'bad12':bad}[entry['pin']]
        if circuit is not None:
            units=module.pins(meta,circuit);cnf.clauses.extend(units)
            meta.update(pinned_circuit=circuit,pin_clause_count=len(units),scope='Fully pinned finite control only; not generic synthesis.')
        raw=cnf.raw();meta.update(clauses=len(cnf.clauses),cnf_sha256=digest(raw))
        metadata=(json.dumps(meta,indent=2,sort_keys=True)+'\n').encode()
        require(len(raw)==entry['bytes'] and digest(raw)==entry['sha256'],'CNF recipe mismatch '+entry['name'])
        require(digest(metadata)==entry['metadata_sha256'],'metadata recipe mismatch '+entry['name'])
        for alias in entry['aliases']:
            p=under(root,alias)
            require(p.with_suffix('.json').read_bytes()==metadata,'metadata alias mismatch '+alias)
            if p.exists():require(p.read_bytes()==raw and not p.is_symlink(),'existing restored CNF mismatch '+alias)
            else:
                with p.open('xb') as f:f.write(raw)
            restored.append(alias)
    require(set(restored)==set(manifest['omitted_cnfs']),'CNF alias inventory')
    for name,expected in manifest['omitted_cnfs'].items():require(info(under(root,name))==expected,'restored CNF mismatch '+name)
    require({str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}==set(payload)|set(restored)|{'MANIFEST.json'},'unexpected extracted file')
    bindings=0
    own=root/'scratch/orch/S06'
    for filename in ['gadget8-handoff.json','gadget8-runner-review-handoff.json']:
        handoff=json.loads((own/filename).read_text())
        for name,expected in handoff['files'].items():
            require(info(under(own,name))==expected,'historical handoff binding '+name);bindings+=1
    for original,entry in manifest['source_map'].items():
        require(info(under(root,entry['path']))=={'bytes':entry['bytes'],'sha256':entry['sha256']},'source-map binding '+original)
    return {'status':'PASS_ARCHIVE_PAYLOADS_FOUR_CNFS_AND_ALL_HISTORICAL_BINDINGS','payloads':len(payload),'unique_cnf_recipes':len(recipes['recipes']),'restored_cnf_aliases':len(restored),'historical_handoff_bindings':bindings,'source_map_bindings':len(manifest['source_map']),'solver_or_checker_launched':False}

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('root',type=Path);args=p.parse_args()
    print(json.dumps(restore(args.root.absolute()),indent=2,sort_keys=True))
