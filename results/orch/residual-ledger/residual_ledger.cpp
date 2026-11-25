#include <algorithm>
#include <cstdint>
#include <iostream>
#include <unordered_map>
#include <vector>
struct Wire { uint64_t tt; unsigned reach; bool isOr; unsigned a=0,b=0; };
struct Graph { unsigned edges; unsigned tau; unsigned bound; uint64_t tt; };
int p,l,n,maxd; unsigned leftMask,rightMask; uint64_t visited=0,candidates=0; std::vector<Wire> wires; std::vector<Graph> graphs; std::unordered_map<uint64_t,std::vector<int>> bytt;
unsigned pop(unsigned a) { return __builtin_popcount(a); }
uint64_t orTT(unsigned mask) { uint64_t z=0; for(unsigned x=0;x<(1u<<n);++x)if(x&mask)z|=uint64_t(1)<<x;return z; }
bool ledger(Graph const& g) {
 unsigned neigh[12]={}, supp[40]={}; std::vector<unsigned> roots[12];
 for(int a=0;a<p;++a)for(int b=0;b<l;++b)if(g.edges&(1u<<(a*l+b))){neigh[a]|=1u<<(p+b);neigh[p+b]|=1u<<a;}
 for(unsigned j=n;j<wires.size();++j)if(wires[j].isOr){
  for(int i=0;i<n;++i)if((wires[j].tt>>(1u<<i))&1)supp[j]|=1u<<i;
  if(pop(supp[j])<2 || orTT(supp[j])!=wires[j].tt)continue;
  for(int c=0;c<n;++c)if(!(supp[j]&~neigh[c]))roots[c].push_back(supp[j]);
 }
 unsigned S[12]={}, comps=0, covered=0, sumS=0;
 for(int c=0;c<n;++c){
  for(auto r:roots[c])S[c]|=r;
  sumS+=pop(S[c]);
  unsigned remaining=S[c];
  while(remaining){unsigned cc=remaining&-remaining,old;do{old=cc;for(auto r:roots[c])if(r&cc)cc|=r;}while(cc!=old);remaining&=~cc;++comps;}
  for(int v=0;v<n;++v)if(S[c]&(1u<<v)){int a=c<p?c:v,b=c<p?v-p:c-p;covered|=1u<<(a*l+b);}
 }
 if(covered!=g.edges)return false;
 ++candidates;
 unsigned owned=0;
 for(unsigned j=n;j<wires.size();++j)if(wires[j].isOr && pop(supp[j])>=2){for(int c=0;c<n;++c)if(!(supp[j]&~S[c])){++owned;break;}}
 unsigned delta=sumS-pop(g.edges),size=wires.size()-n;
 if(comps+g.tau>size-owned+delta+1){
  std::cout<<"RESIDUAL COUNTEREXAMPLE p="<<p<<" l="<<l<<" E="<<g.edges<<" size="<<size<<" tau="<<g.tau<<" sumk="<<comps<<" U="<<owned<<" delta="<<delta<<std::endl;
  for(int c=0;c<n;++c){std::cout<<"centre "<<c<<" S="<<S[c]<<" roots";for(auto r:roots[c])std::cout<<" "<<r;std::cout<<"\n";}
  for(unsigned h=n;h<wires.size();++h)std::cout<<h<<" "<<(wires[h].isOr?"OR":"AND")<<" "<<wires[h].a<<" "<<wires[h].b<<" support="<<supp[h]<<"\n";
  std::exit(2);
 }
 return true;
}
void dfs(int d) {
 ++visited;
 for(unsigned i=n;i<wires.size();++i){auto it=bytt.find(wires[i].tt);if(it!=bytt.end())for(int k:it->second)ledger(graphs[k]);}
 if(d==maxd)return;
 unsigned count=wires.size();
 for(unsigned a=0;a<count;++a)for(unsigned b=a;b<count;++b)for(int op=0;op<2;++op){
  Wire w{op?(wires[a].tt|wires[b].tt):(wires[a].tt&wires[b].tt),op?(wires[a].reach|wires[b].reach):0u,op==1};
  if((w.reach&leftMask)&&(w.reach&rightMask))continue;
  bool dup=false;for(auto const&v:wires)if(v.tt==w.tt && v.reach==w.reach && v.isOr==w.isOr){dup=true;break;}if(dup)continue;
  w.a=a;w.b=b;wires.push_back(w);dfs(d+1);wires.pop_back();
 }
}
int main(){for(auto sz:std::vector<std::pair<int,int>>{{2,2},{2,3}}){p=sz.first;l=sz.second;n=p+l;leftMask=(1u<<p)-1;rightMask=((1u<<l)-1)<<p;graphs.clear();bytt.clear();wires.clear();maxd=0;visited=0;candidates=0;
for(unsigned e=1;e<(1u<<(p*l));++e){bool bad=false;for(int a=0;a<p;++a)for(int a2=a+1;a2<p;++a2){unsigned common=0;for(int b=0;b<l;++b)if((e&(1u<<(a*l+b)))&&(e&(1u<<(a2*l+b))))++common;if(common>=2)bad=true;}if(bad)continue;
for(int a=0;a<p;++a)for(int b=0;b<l;++b)if(e&(1u<<(a*l+b))){unsigned da=0,db=0;for(int c=0;c<l;++c)da+=!!(e&(1u<<(a*l+c)));for(int c=0;c<p;++c)db+=!!(e&(1u<<(c*l+b)));if(da==1&&db==1)bad=true;}if(bad)continue;
unsigned tau=n;for(unsigned s=0;s<(1u<<n);++s){bool cv=true;for(int a=0;a<p;++a)for(int b=0;b<l;++b)if((e&(1u<<(a*l+b)))&&!(s&(1u<<a))&&!(s&(1u<<(p+b))))cv=false;if(cv)tau=std::min(tau,pop(s));}
uint64_t tt=0;for(unsigned x=0;x<(1u<<n);++x)for(int a=0;a<p;++a)for(int b=0;b<l;++b)if((e&(1u<<(a*l+b)))&&(x&(1u<<a))&&(x&(1u<<(p+b))))tt|=uint64_t(1)<<x;
unsigned bound=pop(e)+tau-1;bytt[tt].push_back(graphs.size());graphs.push_back({e,tau,bound,tt});maxd=std::max(maxd,int(bound)-1);
}
maxd=(n==4?6:5);for(int i=0;i<n;++i)wires.push_back({orTT(1u<<i),1u<<i,false});dfs(0);std::cout<<"p="<<p<<" l="<<l<<" targets="<<graphs.size()<<" max_gates="<<maxd<<" states="<<visited<<" target_hits="<<candidates<<" no counterexample\n";
}}
