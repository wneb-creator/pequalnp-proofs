"""Portable restoration and scalar/model validation; never starts a solver."""
from pathlib import Path,PurePosixPath
import argparse,json,hashlib,tarfile,importlib.util,sys,time
sys.dont_write_bytecode=True
def sha(raw):return hashlib.sha256(raw).hexdigest()
def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module
def main():
    ap=argparse.ArgumentParser();ap.add_argument('archive',type=Path);ap.add_argument('fresh_restore',type=Path);args=ap.parse_args();t=time.monotonic()
    assert not args.fresh_restore.exists() and not args.fresh_restore.is_symlink();args.fresh_restore.mkdir(parents=True)
    files={}
    with tarfile.open(args.archive) as tf:
        for m in tf.getmembers():
            p=PurePosixPath(m.name);assert m.isfile() and not p.is_absolute() and '..' not in p.parts and m.name not in files
            b=tf.extractfile(m).read();assert not b.startswith(b'\x7fELF');files[m.name]=b
    manifest=json.loads(files['manifest.json']);assert set(files)=={'manifest.json'}|{r['path'] for r in manifest['files']}
    for r in manifest['files']:
        b=files[r['path']];assert sha(b)==r['sha256'] and len(b)==r['bytes']
    for name,b in files.items():
        p=args.fresh_restore/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
    G=load('archived_gadget7_generator',args.fresh_restore/'build_gadget7.py');V=load('archived_gadget7_validator',args.fresh_restore/'validate_gadget7.py')
    positive,bad=G.circuit_controls();restored=[]
    for recipe in json.loads(files['cnf-recipes.json']):
        cnf,meta=G.build(recipe['gates']);circuit=positive if recipe['pinned']=='positive12' else bad if recipe['pinned']=='bad11' else None
        if circuit is not None:
            units=G.pins(meta,circuit);cnf.clauses.extend(units);meta.update(pinned_circuit=circuit,pin_clause_count=len(units),scope='Fully pinned finite control only; not generic synthesis.')
        raw=cnf.raw();meta.update(clauses=len(cnf.clauses),cnf_sha256=sha(raw));meta_raw=(json.dumps(meta,indent=2,sort_keys=True)+'\n').encode()
        assert sha(raw)==recipe['sha256'] and len(raw)==recipe['bytes']
        assert meta_raw==files[recipe['path'].removesuffix('.cnf')+'.json']
        (args.fresh_restore/recipe['path']).write_bytes(raw);restored.append(dict(path=recipe['path'],sha256=sha(raw),bytes=len(raw)))
    handoff=json.loads(files['gadget7-handoff.json'])
    for name,binding in handoff['files'].items():
        b=(args.fresh_restore/name).read_bytes();assert len(b)==binding['bytes'] and sha(b)==binding['sha256']
    validations=[]
    for model in ['positive12.model.stdout','positive12-pinned-solver.stdout']:
        base=args.fresh_restore/'gadget7-v1';cnf=(base/'positive12-pinned.cnf').read_bytes();meta=(base/'positive12-pinned.json').read_bytes()
        d=V.validate(cnf,meta,(base/model).read_bytes(),sha(cnf),sha(meta));assert d['verified_inputs']==128 and d['full11_verified_inputs']==2048 and d['gate_count']==12 and d['full11_gate_count']==22
        assert d['meets_gadget_11_gate_limit'] is False and d['meets_full21_gate_limit'] is False
        validations.append(dict(model=model,local_inputs=128,full_inputs=2048,gates=12,full_gates=22))
    base=args.fresh_restore/'gadget7-v1';cnf=(base/'bad11-pinned.cnf').read_bytes();meta=(base/'bad11-pinned.json').read_bytes()
    try:V.validate(cnf,meta,(base/'bad11.model.stdout').read_bytes(),sha(cnf),sha(meta))
    except ValueError as e:rejected=str(e)
    else:raise AssertionError('bad11 accepted')
    print(json.dumps(dict(status='PASS_ALL_HASHES_FOUR_CNF_RECONSTRUCTIONS_AND_MODELS',archive_sha256=sha(args.archive.read_bytes()),members=len(files),restored=restored,historical_handoff_bindings=len(handoff['files']),positive_validations=validations,bad11_rejection=rejected,elapsed_seconds=time.monotonic()-t,solver_or_checker_started=False)))
if __name__=='__main__':main()
