import argparse,ast,hashlib,json,shutil,subprocess
from pathlib import Path
BASE=Path('/tmp/oec/pequalnp-pilot-62')
ap=argparse.ArgumentParser();ap.add_argument('input_stem');ap.add_argument('output_stem');ap.add_argument('--base-gzip',required=True);ap.add_argument('--base-sha256',required=True);ap.add_argument('--seal',action='store_true');args=ap.parse_args()
source=Path(args.input_stem);target=Path(args.output_stem)
base_mapping_bytes=source.with_suffix('.mapping.json').read_bytes();mapping=json.loads(base_mapping_bytes)
original_variables=mapping['variables'];original_clauses=mapping['clauses'];groups=mapping['signature_variables'];assert len(groups)%2==0
k=len(groups)//2;bits=len(mapping['positive_samples']);assert all(len(s)==bits for s in groups)
assert all(type(v) is bool or (type(v) is int and 0<v<=original_variables) for s in groups for v in s)
tree=ast.parse((BASE/'multi_output_direct_cnf.py').read_text());node=next(n for n in tree.body if isinstance(n,ast.ClassDef) and n.name=='CNF');scope={'Path':Path,'shutil':shutil};exec(compile(ast.Module(body=[node],type_ignores=[]),'audited_CNF','exec'),scope)
delta=target.with_suffix('.delta.cnf');cnf=scope['CNF'](delta);cnf.variables=original_variables
unions=[[cnf.disj([a,b]) for a,b in zip(groups[2*g],groups[2*g+1])] for g in range(k)]
for gate in range(2,k):
    previous=unions[gate-1];current=unions[gate]
    depends=[cnf.conj(cnf.disj([cnf.neg(a),b]) for a,b in zip(sig,previous)) for sig in groups[2*gate:2*gate+2]]
    equal=True;less=[]
    for a,b in reversed(list(zip(previous,current))):
        less.append(cnf.conj([equal,cnf.neg(a),b]))
        equal=cnf.conj([equal,cnf.disj([cnf.neg(a),b]),cnf.disj([a,cnf.neg(b)])])
    cnf.add(depends+less+[equal])
cnf.finish()
mapping['variables']=cnf.variables;mapping['clauses']=original_clauses+cnf.clauses
mapping['adjacent_independent_order']=True
mapping['ordering_delta_base_variables']=original_variables
mapping['ordering_delta_base_clauses']=original_clauses
mapping['ordering_delta_clauses']=cnf.clauses
mapping['ordering_delta_base_mapping_sha256']=hashlib.sha256(base_mapping_bytes).hexdigest()
mapping_path=target.with_suffix('.mapping.json');mapping_path.write_text(json.dumps(mapping,indent=2)+'\n')
composer=BASE/'compose_ordered_cnf.py'
manifest={'format':'ordered-cnf-composition-v1','base_gzip':str(Path(args.base_gzip).resolve()),
 'base_uncompressed_sha256':args.base_sha256,'base_variables':original_variables,'base_clauses':original_clauses,
 'variables':cnf.variables,'delta_clauses':cnf.clauses,'delta_path':str(delta.resolve()),
 'delta_sha256':hashlib.sha256(delta.read_bytes()).hexdigest(),'mapping_path':str(mapping_path.resolve()),
 'mapping_sha256':hashlib.sha256(mapping_path.read_bytes()).hexdigest(),'composer_script':str(composer),
 'composer_sha256':hashlib.sha256(composer.read_bytes()).hexdigest(),
 'generator_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 'CNF_class_source_sha256':hashlib.sha256((BASE/'multi_output_direct_cnf.py').read_bytes()).hexdigest()}
target.with_suffix('.composition.json').write_text(json.dumps(manifest,indent=2)+'\n')
if args.seal:
    checksum=hashlib.sha256()
    with target.with_suffix('.compose-verification.log').open('w') as log:
        process=subprocess.Popen(['python3',str(composer),str(target.with_suffix('.composition.json'))],stdout=subprocess.PIPE,stderr=log)
        try:
            while chunk:=process.stdout.read(1048576):checksum.update(chunk)
            assert process.wait()==0
        finally:
            process.stdout.close()
            if process.poll() is None:process.kill();process.wait()
    manifest['composed_uncompressed_sha256']=checksum.hexdigest()
    target.with_suffix('.composition.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'or_count':k,'base_variables':original_variables,'new_variables':cnf.variables-original_variables,
 'base_clauses':original_clauses,'new_clauses':cnf.clauses,'delta_bytes':delta.stat().st_size}))
