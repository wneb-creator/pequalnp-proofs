from pathlib import Path
import json,re,hashlib
root=Path(__file__).resolve().parents[1]
src=(root/'lemmas/Weak20369Cofactors.lean').read_text()
assert hashlib.sha256(src.encode()).hexdigest()=='5d5400b5fe31912e43a0581ef421f0b435a79f8d89c0933cd819360b79e53f1f'
fixture=json.loads((root/'search/mono18-certificate-measurement/mono18-weak-dag/complete-fixture-20369.json').read_text())
records=json.loads((root/'weak20369-cut-data.json').read_text())
signals={int(k):int(v,16) for k,v in fixture['signals'].items()}
declared={int(k):int(v,16) for k,v in re.findall(r'def s(\d+) : Sig := (0x[0-9a-f]+)',(root/'lemmas/Weak20369Data.lean').read_text())}
cpp=(root/'search/mono18-certificate-measurement/copy_search_first_prooftrace.cpp').read_text()
profiles=[tuple(map(int,x)) for x in re.findall(r'\{(\d+),(\d+),(\d+),(\d+)\}',cpp.split('static const CP profiles[CP_COUNT] = ',1)[1].split(';',1)[0])]
inputs=[sum(1<<r for r in range(1024) if r>>i&1) for i in range(10)]
assert all(signals[i+1]==w for i,w in enumerate(inputs))
def history(es,i):
    e=es[i]
    if e['left']<0:return []
    a,b=e['left'],e['right']
    return history(es,a)+history(es,b)+[[e['op'],es[a]['signal'],es[b]['signal'],e['signal']]]
out=[]
for rec in records:
    stem=rec['kind'];n=rec['num'];suffix=str(n)
    if stem=='terminal':
        node=fixture['nodes'][suffix];witness=node['done'];assert witness['kind']=='cofactor'
        state=node['node']['state'];cap=node['node']['remaining'];hist=node['node']['history']
    else:
        assert stem=='gate';node=fixture['nodes']['9611'];witness=node['cuts'][n]
        es=node['entries'];a,b=witness['left'],witness['right'];basis=node['basis']
        counts=[x+y for x,y in zip(es[a]['counts'],es[b]['counts'])]
        state=[r for r,t,c in zip(basis['roots'],basis['total'],counts) for _ in range(t-c)]+[witness['signal']]
        hist=node['node']['history']+history(es,a)+history(es,b)+[[witness['op'],es[a]['signal'],es[b]['signal'],witness['signal']]]
        cap=witness['remaining']
    assert state==rec['ws'] and cap==rec['cap'] and witness['profile']==rec['profile'] and witness['lower']==rec['lower']
    assert rec['choices']==[hist[i] for i in witness['selected_history']]
    ws=list(map(int,re.findall(r's(\d+)',re.search(r'def '+stem+'Ws'+suffix+r' : List Sig := \[([^\n]*)\]',src).group(1))))
    choices=[list(map(int,t)) for t in re.findall(r'\((\d+), s(\d+), s(\d+)\)',re.search(r'def '+stem+'Choices'+suffix+r' : List Choice := \[([^\n]*)\]',src).group(1))]
    assert ws==state and choices==[g[:3] for g in rec['choices']]
    p1,p2,printedcap=map(int,re.search(r'theorem '+stem+'Check'+suffix+r' : runCofactorCheck false inputs \(Mono18FullProfiles.domain (\d+)\)\s*\(Mono18FullProfiles.bound (\d+)\) (\d+)',src).groups())
    assert p1==p2==rec['profile'] and printedcap==cap
    assert 'runCofactorCheck_sound (Mono18FullProfiles.slice '+str(p1)+') '+stem+'Check'+suffix+' bound' in src
    assert re.search(r'theorem '+stem+'Run'+suffix+r' \{k : Nat\} \(bound : k ≤ '+str(cap)+r'\)',src)
    pool=set(range(1,11))
    for d,a,b,z in hist:
        assert a in pool and b in pool and d in (0,1)
        assert signals[z]==(signals[a]&signals[b] if d==0 else signals[a]|signals[b]);pool.add(z)
    assert all(v in pool for v in state)
    used=set(state)|{v for g in choices for v in g[1:]}
    assert all(declared[v]==signals[v] for v in used)
    zeros,ones,_,lower=profiles[p1];assert lower==rec['lower'] and p1!=1086
    mask=sum(1<<r for r in range(1024) if r&zeros==0 and r&ones==ones)
    projected={0,mask}|{v&mask for v in inputs}
    for d,a,b in choices:
        assert signals[a]&mask in projected and signals[b]&mask in projected
        projected.add((signals[a]&signals[b] if d==0 else signals[a]|signals[b])&mask)
    assert all(signals[v]&mask in projected for v in state)
    mass=sum(signals[v]&mask in (0,mask) for v in state)
    assert mass==witness['mass'] and lower+mass>cap+len(choices)
    out.append(dict(kind=stem,num=n,profile=p1,lower=lower,cap=cap,mass=mass,paid=len(choices),margin=lower+mass-cap-len(choices)))
assert len(out)==15 and sum(r['kind']=='terminal' for r in out)==10
assert (root/'lemmas/Weak20369Cofactors.compile.txt').read_text().strip() in ('','Compiler exit code: 0')
assert not re.search(r'\b(sorry|axiom|native_decide|bv_decide|unsafe|partial|structure|inductive|instance)\b|_root_|"|@\[(?!simp)',src)
print(json.dumps(dict(verdict='PASS',source_sha256=hashlib.sha256(src.encode()).hexdigest(),exact_frozen_fixture=True,all_1024_bit_histories=True,records=out,scope='Ten terminal and five omitted-gate bounded Run exclusions; parent DAG/gluing is separate.'),indent=2))
