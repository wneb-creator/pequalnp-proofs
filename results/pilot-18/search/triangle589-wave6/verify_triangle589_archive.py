"""Portable byte and finite-seed verifier; reads tar members, runs no engine."""
from pathlib import Path
import argparse,json,hashlib,tarfile,time
EDGES=[(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
def sha(b):return hashlib.sha256(b).hexdigest()
def main():
    ap=argparse.ArgumentParser();ap.add_argument('archive',type=Path);ap.add_argument('--report',type=Path,required=True);args=ap.parse_args();t=time.monotonic()
    with tarfile.open(args.archive,'r:gz') as tar:
        members=tar.getmembers();assert all(m.isfile() and not m.name.startswith('/') and '..' not in Path(m.name).parts for m in members)
        assert len({m.name for m in members})==len(members)
        files={m.name:tar.extractfile(m).read() for m in members}
    manifest=json.loads(files['manifest.json']);assert len(manifest['files'])==len(files)-1
    for entry in manifest['files']:
        b=files[entry['member']];assert len(b)==entry['bytes'] and sha(b)==entry['sha256'] and not b.startswith(b'\x7fELF');b.decode('utf-8')
    target=[any(m>>a&1 and m>>b&1 for a,b in EDGES) for m in range(2048)]
    def eval_data(d,m):
        vals=[bool(m>>i&1) for i in range(11)]
        if d['gate_wire_offset']==13:vals+=[False,True]
        for op,a,b in d['gates']:vals.append(vals[a]&vals[b] if op=='and' else vals[a]|vals[b])
        return vals
    output_checks=intermediate_checks=0;reviews=[]
    for name,count,pin,is_best in [('triangle589-direct21-v1',16,'a7b9083ef7737ffedc1e35cafb46bdbbb6c74ca909d7550b0633174dc4315fdc',False),('triangle589-best3-direct21-v1',8,'6c60f7617f1b797fd8408ddbf5f08d94a148c2c49eb66d9821d7f35e68606e9b',True)]:
        base='scratch/orch/S05/'+name+'/';metadata=json.loads(files[base+'direct-seeds.json']);pack=files[base+'direct-seeds.txt'];assert sha(pack)==pin==metadata['pack_sha256']
        assert metadata['count']==count
        tokens=pack.decode().split();assert tokens[:3]==['COVER_ANNEAL_DIRECT21','1',str(count)];at=3;orders=set()
        for entry in metadata['seeds']:
            seed_path=base+Path(entry['path']).name;seed=json.loads(files[seed_path]);assert sha(files[seed_path])==entry['sha256']
            if is_best:source=json.loads(files[base+'source.json'])
            else:source=json.loads(files[base+entry['base']+'-original.json'])
            n,output,fn,fp,truth=map(int,tokens[at:at+5]);at+=5;assert (n,output,fn,fp)==(21,seed['output'],0,5 if is_best else 10)
            packed=[]
            for g in range(21):
                op,a,b=map(int,tokens[at:at+3]);at+=3;assert op in (0,1) and 0<=a<=b<13+g;packed.append(['and' if op else 'or',a,b])
            assert packed==seed['gates'];orders.add(tuple(entry['new_to_old']));h=14695981039346656037;actual_fp=actual_fn=0
            for m in range(2048):
                before=eval_data(source,m);after=eval_data(seed,m);actual=after[output]
                expected=target[m] or bool(m>>2&1 and (m>>4&1 if is_best else m&18) and m&129)
                assert actual==expected==before[source['output']];output_checks+=1
                for new,old in enumerate(entry['new_to_old']):assert after[13+new]==before[source['gate_wire_offset']+old];intermediate_checks+=1
                actual_fn+=target[m] and not actual;actual_fp+=not target[m] and actual;h=((h^actual)*1099511628211)&((1<<64)-1)
            assert (actual_fn,actual_fp,h)==(fn,fp,truth)
        assert at==len(tokens)
        if is_best:assert len(orders)==8
        reviews.append(dict(pack=name,count=count,sha256=pin,full_fn=0,full_fp=5 if is_best else 10))
    assert output_checks==49152 and intermediate_checks==1032192
    result=dict(status='PASS_PORTABLE_TRIANGLE589_ARCHIVE',archive_sha256=sha(args.archive.read_bytes()),manifest_sha256=sha(files['manifest.json']),members=len(files),bound_payloads=len(manifest['files']),all_regular=True,no_compiled_binaries=True,packed_input_checks=output_checks,intermediate_checks=intermediate_checks,packs=reviews,engine_executed=False,elapsed_seconds=time.monotonic()-t)
    with args.report.open('x') as f:json.dump(result,f,indent=2);f.write('\n')
    print(json.dumps(result))
if __name__=='__main__':main()
