import itertools,json,sys
from pathlib import Path

def tables(n):
    rows=1<<n
    allones=(1<<rows)-1
    return [((allones//((1<<(2*(1<<j)))-1))*(((1<<(1<<j))-1)<<(1<<j))) for j in range(n)]

def graph_info(n,edges):
    adj=[0]*n
    assert len(set(tuple(sorted(e)) for e in edges))==len(edges)
    for a,b in edges:
        assert 0<=a<n and 0<=b<n and a!=b
        adj[a]|=1<<b;adj[b]|=1<<a
    assert all((adj[a]&adj[b]).bit_count()<=1 for a in range(n) for b in range(a+1,n)), 'C4 found'
    independent=bytearray(1<<n);independent[0]=1;alpha=0;maxset=0
    for s in range(1,1<<n):
        low=s&-s;r=s-low;j=low.bit_length()-1
        if independent[r] and not(adj[j]&r):
            independent[s]=1
            if s.bit_count()>alpha:alpha=s.bit_count();maxset=s
    return adj,n-alpha,((1<<n)-1)^maxset

def eval_gates(n,gates):
    v=tables(n)
    for j,(op,a,b) in enumerate(gates):
        assert op in ('and','or') and 0<=a<n+j and 0<=b<n+j
        v.append((v[a]&v[b]) if op=='and' else (v[a]|v[b]))
    return v

log=Path(sys.argv[1]);lines=log.read_text().splitlines()
starts=[i for i,l in enumerate(lines) if l.startswith('GADGET WITNESS ')]
if not starts:
    print('NO WITNESS');raise SystemExit(0)
i=starts[-1];tokens=lines[i].split()[2:];fields={tokens[k]:int(tokens[k+1]) for k in range(0,len(tokens),2)}
n=fields.get('n',6);gout=fields['output'];orig={};marked=set();aux=[]
for line in lines[i+1:]:
    xs=line.split()
    if not xs:continue
    if xs[0]=='aux':aux.append((int(xs[1]),int(xs[3])))
    elif xs[0].isdigit():
        j=int(xs[0]);orig[j]=[xs[1],int(xs[2]),int(xs[3])]
        if int(xs[5]):marked.add(j)
assert len(aux)==fields['auxcount']
assert sorted(orig)==list(range(n,n+len(orig)))
oldgates=[orig[j] for j in sorted(orig)];values=eval_gates(n,oldgates)
pairs=list(itertools.combinations(range(n),2));edges=[list(pairs[j]) for j in range(len(pairs)) if fields['graph']>>j&1]
adj,tau,oldcover=graph_info(n,edges)
assert tau==fields['tau'] and len(edges)==fields['edges']
truth=0
for a,b in edges:truth|=values[a]&values[b]
assert values[gout]==truth
live=set()
def visit(j):
    if j<n or j in live:return
    assert j in orig;live.add(j);visit(orig[j][1]);visit(orig[j][2])
visit(gout)
for j,s in aux:
    assert s<(1<<n) and s.bit_count()>=2
    expected=0
    members=[a for a in range(n) if s>>a&1]
    for a in members:expected|=values[a]
    assert values[j]==expected
    assert all(not(adj[a]&adj[b]) for a,b in itertools.combinations(members,2))
    visit(j)
assert all((s&t).bit_count()<=1 for (_,s),(_,t) in itertools.combinations(aux,2))
assert live==marked and len(live)==fields['livecost']
newn=n+2*len(aux);assert newn<=24,'use separate large-n verifier'
newgates=[];wiremap={j:j for j in range(n)}
for j in sorted(live):
    op,a,b=orig[j];newgates.append([op,wiremap[a],wiremap[b]]);wiremap[j]=newn+len(newgates)-1
output=wiremap[gout];newedges=[e[:] for e in edges]
for k,(j,s) in enumerate(aux):
    center=n+2*k;leaf=center+1
    for a in range(n):
        if s>>a&1:newedges.append([a,center])
    newedges.append([center,leaf])
    newgates.append(['or',wiremap[j],leaf]);u=newn+len(newgates)-1
    newgates.append(['and',center,u]);v=newn+len(newgates)-1
    newgates.append(['or',output,v]);output=newn+len(newgates)-1
newadj,newtau,newcover=graph_info(newn,newedges)
assert newtau==tau+len(aux)
assert len(newgates)==len(live)+3*len(aux)
newvalues=eval_gates(newn,newgates);newtruth=0
for a,b in newedges:newtruth|=newvalues[a]&newvalues[b]
assert newvalues[output]==newtruth,'extended truth-table mismatch'
gain=len(newedges)+newtau-1-len(newgates)
assert gain==fields['gain'] and gain>0
result={'n':newn,'edges':newedges,'tau':newtau,'cover_mask':newcover,'gates':newgates,'output':output,'size':len(newgates),'bound':len(newedges)+newtau-1,'gap':gain,'truth_rows_checked':1<<newn,'all_vertex_subsets_checked':1<<newn,'base_n':n,'base_output':gout,'auxiliaries':aux,'source_log':str(log)}
out=Path(sys.argv[2]);out.write_text(json.dumps(result,indent=2)+'\n')
print('VERIFIED EXTENDED WITNESS',json.dumps({k:result[k] for k in ['n','tau','size','bound','gap','truth_rows_checked']}))
