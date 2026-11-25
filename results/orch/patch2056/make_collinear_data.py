from pathlib import Path
import json
base=Path(__file__).resolve().parent
points=[0,1,2,3,4,9];D={0,1,3,9}
for name,lines in [('collinear6',list(range(13))),('core14',[l for l in range(13) if sum((p+l)%13 in D for p in points)>=2])]:
 N=len(points);n=N+len(lines);edges=[(i,N+j) for i,p in enumerate(points) for j,l in enumerate(lines) if (p+l)%13 in D]
 ns=[sum(1<<(b-N) for a,b in edges if a==i) for i in range(N)];negative=set()
 for s in range(1<<N):
  nb=0
  for i in range(N):
   if s>>i&1:nb|=ns[i]
  t=((1<<len(lines))-1)^nb;ss=sum(1<<i for i in range(N) if ns[i]&t==0);negative.add(ss|(t<<N))
 rows=[(1<<a)|(1<<b) for a,b in edges]+sorted(negative)
 gs=[];roots=[]
 for p in range(N):
  neighbors=[b for a,b in edges if a==p];v=neighbors[0]
  for b in neighbors[1:]:gs.append([1,v,b]);v=n+len(gs)-1
  gs.append([0,p,v]);roots.append(n+len(gs)-1)
 v=roots[0]
 for b in roots[1:]:gs.append([1,v,b]);v=n+len(gs)-1
 for r in rows:
  vals=[bool(r>>i&1) for i in range(n)]
  for op,a,b in gs:vals.append(vals[a]|vals[b] if op else vals[a]&vals[b])
  assert vals[-1]==any(r>>a&1 and r>>b&1 for a,b in edges)
 data={'points':points,'lines':lines,'inputs':n,'edges':edges,'rows':rows,'gates':gs,'output':v,'baseline':len(gs),'target':len(gs)-1}
 (base/(name+'-data.json')).write_text(json.dumps(data,indent=2)+'\n')
 (base/(name+'-rows.txt')).write_text(''.join(str(r)+'\n' for r in rows))
 (base/(name+'-control.txt')).write_text(''.join(f'{op} {a} {b}\n' for op,a,b in gs))
 print(name,{'inputs':n,'edges':len(edges),'maxfalse':len(negative),'baseline':len(gs),'target':len(gs)-1})
s=(base/'six_structured.cpp').read_text().replace('#include "six_seeds.hpp"\n','')
s=s.replace('constexpr int N=6, LINES=11, INPUTS=17, GATES=28, WIRES=45;\nconstexpr int P[N]={0,1,2,3,6,7};\nconstexpr int Q[LINES]={0,1,2,3,6,7,8,9,10,11,12};','constexpr int N=6, LINES=13, INPUTS=19, GATES=28, WIRES=47;\nconstexpr int P[N]={0,1,2,3,4,9};\nconstexpr int Q[LINES]={0,1,2,3,4,5,6,7,8,9,10,11,12};')
assert 'INPUTS=19' in s
start=s.index('std::vector<Gate> star(');end=s.index('Net deleteGate',start)
star=r'''std::vector<Gate> star(std::mt19937& rng){
 std::vector<Gate> c;std::vector<int> roots;std::vector<bool> take(LINES,false);
 int mode=rng()%4,copiedInput=0,duplicatePoint=0;
 if(mode<2){std::vector<int>ls;for(int l=0;l<LINES;l++){int deg=0;for(int p=0;p<N;p++)deg+=incident(p,l);if(deg>=2)ls.push_back(l);}std::shuffle(ls.begin(),ls.end(),rng);int count=1+rng()%3;for(int k=0;k<count;k++)take[ls[k]]=true;}
 if(mode==2){copiedInput=rng()%INPUTS;int other=rng()%(INPUTS-1);if(other>=copiedInput)other++;c.push_back({1,copiedInput,other});c.push_back({0,copiedInput,INPUTS});duplicatePoint=INPUTS+1;}
 auto inp=[&](int i){return i==copiedInput?duplicatePoint:i;};
 auto addStar=[&](int center,std::vector<int>nb){if(nb.empty())return;std::shuffle(nb.begin(),nb.end(),rng);int a=inp(nb[0]);for(int k=1;k<(int)nb.size();k++){int d=INPUTS+c.size();c.push_back({1,a,inp(nb[k])});a=d;}int d=INPUTS+c.size();c.push_back({0,inp(center),a});roots.push_back(d);};
 std::array<int,N>order;std::iota(order.begin(),order.end(),0);std::shuffle(order.begin(),order.end(),rng);
 for(int p:order){std::vector<int>nb;for(int l=0;l<LINES;l++)if(!take[l]&&incident(p,l))nb.push_back(N+l);addStar(p,nb);}
 for(int l=0;l<LINES;l++)if(take[l]){std::vector<int>nb;for(int p=0;p<N;p++)if(incident(p,l))nb.push_back(p);addStar(N+l,nb);}
 while(roots.size()>1){int ia=rng()%roots.size(),a=roots[ia];roots.erase(roots.begin()+ia);int ib=rng()%roots.size(),b=roots[ib];roots.erase(roots.begin()+ib);int d=INPUTS+c.size();c.push_back({1,a,b});roots.push_back(d);}
 return c;
}
'''
s=s[:start]+star+s[end:]
data=json.loads((base/'collinear6-data.json').read_text());s=s.replace('if(rows.size()!=76)',f'if(rows.size()!={len(data["rows"])})')
(base/'collinear6_structured.cpp').write_text(s)
