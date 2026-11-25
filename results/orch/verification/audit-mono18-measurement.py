from pathlib import Path
from collections import Counter
import hashlib,json,gzip,re,resource,os

resource.setrlimit(resource.RLIMIT_AS,(1_000_000_000,1_000_000_000));os.sched_setaffinity(0,{2})
base=Path(__file__).resolve().parents[1]/'search/mono18-certificate-measurement'
expected='81a5deceb591bcb404d874061527d6e8b7713b7f9bb1fecea8fb007575ebe019'
assert hashlib.sha256((base/'manifest.json').read_bytes()).hexdigest()==expected
manifest=json.loads((base/'manifest.json').read_text());assert len(manifest)==94
assert {p.relative_to(base).as_posix() for p in base.rglob('*') if p.is_file()}==set(manifest)|{'manifest.json'}
gzip_count=0
for name,rec in manifest.items():
    raw=(base/name).read_bytes();assert len(raw)==rec['bytes'] and hashlib.sha256(raw).hexdigest()==rec['sha256']
    if name.endswith('.gz'):
        decoded=gzip.decompress(raw);gzip_count+=1
        if (base/name[:-3]).exists():assert decoded==(base/name[:-3]).read_bytes()
source=(base/'copy_search_first_prooftrace.cpp').read_text()
assert hashlib.sha256(source.encode()).hexdigest()=='b66739a56db722c470d02767c15b3e812f727546268d706df4a14c4442e8c021'
profiles=[tuple(map(int,x)) for x in re.findall(r'\{(\d+),(\d+),(\d+),(\d+)\}',source.split('static const CP profiles[CP_COUNT] = ',1)[1].split(';',1)[0])]
assert len(profiles)==1145
masks=[sum(1<<r for r in range(1024) if r&z==0 and r&o==o) for z,o,_,_ in profiles]
inputs=[sum(1<<r for r in range(1024) if r>>i&1) for i in range(10)]
binding=json.loads((base/'inputs.json').read_text());reports=[]
for mode,archive,repnames in [('strong','mono18-or-edge-fresh-proof',['mono18-strong-weak-replacements.json.gz']),('weak','mono18-or-edge-weak-fresh-proof',['mono18-weak14-replacements.json.gz','mono18-weak-profile1086-replacements.json'])]:
    proofbase=base.parent/archive
    replacement_sets=[];wanted={}
    for name in repnames:
        raw=(base/name).read_bytes(); report=json.loads(gzip.decompress(raw) if name.endswith('.gz') else raw)
        replacement_sets.append((name,report))
        for rec in report['replacements']:
            key=(rec['node'],rec['event'],rec['left'],rec['right'],rec['op'],rec['signal'])
            assert key not in wanted;wanted[key]=rec
    for name,meta in binding[mode].items():
        p=proofbase/name
        if p.exists():raw=p.read_bytes()
        else:raw=gzip.decompress((proofbase/(name+'.gz')).read_bytes())
        assert len(raw)==meta['bytes'] and hashlib.sha256(raw).hexdigest()==meta['sha256']
    del raw
    stack=[];signals={};counts=Counter();done=Counter();completion=[];matched=set();essential=0;retained=0;subcuts=0;singlezeros=0
    def history(es,i):
        e=es[i]
        if e['left']<0:return []
        a,b=e['left'],e['right'];return history(es,a)+history(es,b)+[[e['op'],es[a]['signal'],es[b]['signal'],e['signal']]]
    with gzip.open(proofbase/'proof.jsonl.gz','rt') as f:
        for line in f:
            e=json.loads(line);typ=e['event'];counts[typ]+=1
            if typ=='node':stack.append(dict(node=e,entries=[],cuts=0))
            elif typ=='signal':signals[e['id']]=int(e['hex'],16)
            elif typ=='basis':stack[-1]['basis']=e
            elif typ=='entry':stack[-1]['entries'].append(e)
            if typ=='subtree_cut' or (typ=='done' and e['kind']=='cofactor'):
                singlezeros+=e['profile']<10
                n=stack[-1];key=(e.get('node',e.get('id')),typ,e.get('left'),e.get('right'),e.get('op'),e.get('signal'))
                if key in wanted:
                    rec=wanted[key];assert rec['original_profile']==e['profile']
                    if typ=='done':state=n['node']['state'];rem=n['node']['remaining'];hist=n['node']['history']
                    else:
                        es=n['entries'];a,b=e['left'],e['right'];basis=n['basis'];cs=[x+y for x,y in zip(es[a]['counts'],es[b]['counts'])]
                        state=[r for r,t,c in zip(basis['roots'],basis['total'],cs) for _ in range(t-c)]+[e['signal']]
                        rem=e['remaining'];hist=n['node']['history']+history(es,a)+history(es,b)+[[e['op'],es[a]['signal'],es[b]['signal'],e['signal']]]
                    assert (state,rem,hist)==(rec['state'],rec['remaining'],rec['history']);matched.add(key)
            if typ=='subtree_cut':stack[-1]['cuts']+=1
            elif typ=='done':
                n=stack.pop();assert n['node']['id']==e['id'];done[e['kind']]+=1;completion.append(e['id'])
                if e['kind'] in ('expand','tight_closure'):essential+=1;retained+=len(n['entries']);subcuts+=n['cuts']
    assert not stack and len(matched)==len(wanted)
    summary=json.loads((base/f'mono18-{mode}-dag/summary.json').read_text())
    assert dict(counts)==summary['event_counts'] and dict(done)==summary['terminal_counts']
    assert (essential,retained,subcuts)==(summary['nonterminal_nodes'],summary['retained_entries'],summary['subtree_cut_witnesses'])
    assert completion==json.loads((base/f'mono18-{mode}-dag/completion-order.json').read_text())
    for name,meta in summary['packing'].items():
        raw=(base/f'mono18-{mode}-dag/{name}.varint').read_bytes()
        assert len(raw)==meta['varint_bytes'] and hashlib.sha256(raw).hexdigest()==meta['sha256']
        assert (base/f'mono18-{mode}-dag/{name}.varint.gz').stat().st_size==meta['gzip_bytes']
        # Complete canonical unsigned base128 words, including every trailing byte.
        start=0
        for i,b in enumerate(raw):
            if b<128:
                assert i==start or b!=0;start=i+1
        assert start==len(raw)
    for kind in ['compact','shortlist']:
        layout=json.loads((base/f'mono18-{mode}-dag/{kind}-witness-candidate-layout.json').read_text())
        payload=(base/f'mono18-{mode}-dag/{kind}-witness-candidate.bin').read_bytes()
        assert len(payload)==layout['total_bytes'] and hashlib.sha256(payload).hexdigest()==layout['sha256']
        offset=0
        for part in layout['parts']:
            raw=(base/f'mono18-{mode}-dag'/f"{part['stream']}.varint").read_bytes()
            assert part['offset']==offset and part['length']==len(raw) and payload[offset:offset+len(raw)]==raw;offset+=len(raw)
        assert offset==len(payload)
    replacement_census=[]
    for name,report in replacement_sets:
        same=failed=success=0;lower14='weak14' in name
        for rec in report['replacements']:
            pool=set(range(1,11))
            for d,a,b,z in rec['history']:
                assert d in (0,1) and a in pool and b in pool
                assert signals[z]==(signals[a]&signals[b] if d==0 else signals[a]|signals[b]);pool.add(z)
            assert all(v in pool for v in rec['state'])
            w=rec['replacement']
            if w is None:failed+=1;continue
            success+=1;same+=w['profile']==rec['original_profile'];p=w['profile'];mask=masks[p]
            lower=14 if lower14 and p<10 else profiles[p][3]
            assert lower==w['lower'] and w['budget']==rec['remaining']
            chosen=w['selected_history'];assert chosen==sorted(set(chosen)) and len(chosen)==w['paid']
            projected={0,mask}|{v&mask for v in inputs}
            for i in chosen:
                d,a,b,z=rec['history'][i];assert signals[a]&mask in projected and signals[b]&mask in projected;projected.add(signals[z]&mask)
            assert all(signals[v]&mask in projected for v in rec['state'])
            mass=sum(signals[v]&mask in (0,mask) for v in rec['state'])
            assert mass==w['mass'] and lower+mass>rec['remaining']+len(chosen)
        assert failed==report['failed']
        if lower14:
            assert same==0 and report['same_profile']+len(report['replacements'])==report['requested']==singlezeros
        else:
            assert same==report['same_profile'] and len(report['replacements'])==report['requested']
            if 'strong-weak' in name:assert report['requested']==singlezeros
        replacement_census.append(dict(file=name,requested=report['requested'],reported_same=report['same_profile'],recorded_successes_replayed=success,unresolved=failed))
    reports.append(dict(mode=mode,event_counts=dict(counts),nonterminals=essential,entries=retained,subcuts=subcuts,original_singlezero_contexts=singlezeros,replacements=replacement_census))
    del wanted,replacement_sets,signals
print(json.dumps(dict(verdict='PASS',manifest_sha256=expected,manifest_entries=len(manifest),gzip_streams_verified=gzip_count,reports=reports,max_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,scope='Preservation/source review and independent input/count/payload/replacement replay. Failed alternatives remain unresolved, not impossibility proofs. Same-profile lower14 successes are counted from the archived classification, not individually recomputed here. Complete Lean root certificate, codec and all prior proofs remain absent.'),indent=2))
