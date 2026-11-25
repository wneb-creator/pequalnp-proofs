from itertools import combinations
D=frozenset((0,1,3,9))
INC={(p,l) for p in range(13) for l in range(13) if (p+l)%13 in D}
def join(a,b):
    assert a!=b
    out=[l for l in range(13) if (a,l) in INC and (b,l) in INC]
    assert len(out)==1
    return out[0]
def meet(a,b):
    assert a!=b
    out=[p for p in range(13) if (p,a) in INC and (p,b) in INC]
    assert len(out)==1
    return out[0]
def frame(q):
    return len(set(q))==4 and all(join(a,b)!=join(a,c) for a,b,c in combinations(q,3))
def map_pair(a,b):
    assert 0<=a<13 and 0<=b<13 and a!=b
    target=(0,1,2,5)
    assert frame(target)
    source=next((a,b,c,d) for c in range(13) for d in range(13) if frame((a,b,c,d)))
    pm=dict(zip(source,target));lm={}
    def assign(mapping,i,j):
        if i in mapping:assert mapping[i]==j
        else:assert j not in mapping.values();mapping[i]=j
    for roundno in range(8):
        old=(len(pm),len(lm))
        for i,j in combinations(list(pm),2):assign(lm,join(i,j),join(pm[i],pm[j]))
        for i,j in combinations(list(lm),2):assign(pm,meet(i,j),meet(lm[i],lm[j]))
        if old==(len(pm),len(lm)):break
    assert len(pm)==len(lm)==13
    assert {(pm[p],lm[l]) for p,l in INC}==INC
    assert pm[a]==0 and pm[b]==1
    return [pm[i] for i in range(13)],[lm[i] for i in range(13)]
def line_pair_input_permutation(a,b):
    pm,lm=map_pair(a,b)
    result=[13+lm[i] for i in range(13)]+[pm[i] for i in range(13)]
    assert sorted(result)==list(range(26))
    assert result[13+a]==0 and result[13+b]==1
    assert {tuple(sorted((result[p],result[13+l]))) for p,l in INC}=={(p,13+l) for p,l in INC}
    return result
if __name__=='__main__':
    import resource,json,hashlib,datetime
    from pathlib import Path
    resource.setrlimit(resource.RLIMIT_CORE,(0,0));resource.setrlimit(resource.RLIMIT_AS,(256*1024**2,256*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(10,10))
    count=0
    for a in range(13):
        for b in range(13):
            if a!=b:line_pair_input_permutation(a,b);count+=1
    result={'scope':'Finite incidence-graph input permutation helper, not a circuit witness or Lean theorem','ordered_line_pairs_verified':count,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
    Path('/tmp/oec/pequalnp-pilot-79/meta3773-projective-normalize-result.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result))
