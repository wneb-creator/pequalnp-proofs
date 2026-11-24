"""Portable hash and scalar verification; never runs an engine or solver."""
from pathlib import Path,PurePosixPath
import argparse,tarfile,hashlib,json,time
E=[(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
def evaluate(d,m):
    n=d['inputs'];offset=d['gate_wire_offset'];v=[bool(m>>i&1) for i in range(n)]
    if offset==n+2:v += [False,True]
    else:assert offset==n
    for i,(op,a,b) in enumerate(d['gates']):
        assert op in ('and','or') and 0<=a<offset+i and 0<=b<offset+i
        v.append(v[a]&v[b] if op=='and' else v[a]|v[b])
    return v
def main():
    ap=argparse.ArgumentParser();ap.add_argument('archive');args=ap.parse_args();t=time.monotonic()
    with tarfile.open(args.archive) as tf:
        files={}
        for member in tf.getmembers():
            p=PurePosixPath(member.name);assert member.isfile() and not p.is_absolute() and '..' not in p.parts
            assert member.name not in files;raw=tf.extractfile(member).read();assert not raw.startswith(b'\x7fELF');files[member.name]=raw
    manifest=json.loads(files['manifest.json']);assert set(files)=={'manifest.json'}|{e['path'] for e in manifest['files']}
    for e in manifest['files']:
        b=files[e['path']];assert len(b)==e['bytes'] and hashlib.sha256(b).hexdigest()==e['sha256']
    target=[any(m>>a&1 and m>>b&1 for a,b in E) for m in range(2048)];expected=[target[m] or bool(m&1 and m&4 and m&16) for m in range(2048)]
    packchecks=intermediates=sourcechecks=0
    for dirname,rotated in [('allnegative-best4-direct21-v1',False),('allnegative-best4-rotated-direct21-v1',True)]:
        meta=json.loads(files['S05/'+dirname+'/direct-seeds.json']);tokens=files['S05/'+dirname+'/direct-seeds.txt'].decode().split();assert tokens[:3]==['COVER_ANNEAL_DIRECT21','1','8'];at=3
        for entry in meta['seeds']:
            size,out,fn,fp,truth=map(int,tokens[at:at+5]);at+=5;assert (size,fn,fp)==(21,0,4);gates=[]
            for i in range(21):
                op,a,b=map(int,tokens[at:at+3]);at+=3;assert op in (0,1) and 0<=a<=b<13+i;gates.append(['and' if op else 'or',a,b])
            d=dict(inputs=11,gate_wire_offset=13,gates=gates,output=out)
            source_name=f'center-{entry["center"]}-original.json' if rotated else 'source.json'
            source=json.loads(files['S05/'+dirname+'/'+source_name]);order=entry['new_to_old'];assert sorted(order)==list(range(21));h=14695981039346656037
            for m in range(2048):
                v=evaluate(d,m);w=evaluate(source,m);assert v[out]==expected[m]==w[source['output']];packchecks+=1
                for new,old in enumerate(order):assert v[13+new]==w[source['gate_wire_offset']+old];intermediates+=1
                h=((h^v[out])*1099511628211)&((1<<64)-1)
            assert h==truth
        assert at==len(tokens)
    for name,kind in [('candidate134227-repair/best1-offset11.json','F_OR9'),('candidate134227-repair/best3-offset11.json','F_MINUS25'),('allnegative-best4-analysis/original-offset11.json','F_OR024'),('allnegative-best4-analysis/exact22-one-gate-control.json','F')]:
        d=json.loads(files['S05/'+name])
        for m in range(2048):
            want=target[m] if kind=='F' else expected[m] if kind=='F_OR024' else target[m] or bool(m>>9&1) if kind=='F_OR9' else any(m>>a&1 and m>>b&1 for a,b in E if (a,b)!=(2,5))
            assert evaluate(d,m)[d['output']]==want;sourcechecks+=1
    gadgetchecks=0
    for n in (7,8):
        d=json.loads(files[f'S05/gadget{n}-contributor-candidate.json']);edges=[(3,4),(3,5),(4,5),(0,3),(1,4),(2,5),(0,6),(1,6),(2,6)]+([(6,7)] if n==8 else [])
        assert d['size']==n+5
        for m in range(1<<n):assert evaluate(d,m)[d['output']]==any(m>>a&1 and m>>b&1 for a,b in edges);gadgetchecks+=1
    print(json.dumps(dict(status='PASS_HASHES_AND_SCALAR_CONTROLS',archive_sha256=hashlib.sha256(Path(args.archive).read_bytes()).hexdigest(),members=len(files),pack_input_checks=packchecks,intermediate_comparisons=intermediates,source_input_checks=sourcechecks,gadget_input_checks=gadgetchecks,elapsed_seconds=time.monotonic()-t,engine_or_search_executed=False)))
if __name__=='__main__':main()
