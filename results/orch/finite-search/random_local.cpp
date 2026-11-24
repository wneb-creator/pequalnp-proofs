#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <set>
#include <vector>
using U=unsigned __int128;
struct Gate { int op,a,b; };
std::uint64_t rng_state;
std::uint64_t rng() {
  std::uint64_t z=(rng_state+=0x9e3779b97f4a7c15ull);
  z=(z^(z>>30))*0xbf58476d1ce4e5b9ull;
  z=(z^(z>>27))*0x94d049bb133111ebull;
  return z^(z>>31);
}
unsigned capsum(unsigned a,unsigned b) {
  unsigned c=0;
  for(unsigned i=0;i<16;++i) if((a>>i)&1)
    for(unsigned j=0;j<16;++j) if((b>>j)&1)
      c|=1u<<(4*std::min(3u,(i>>2)+(j>>2))+std::min(3u,(i&3)+(j&3)));
  return c;
}
int main(int argc,char**argv) {
  if(argc!=6) { std::cerr<<"usage: random_local P L max_gates trials seed\n"; return 2; }
  int P=std::atoi(argv[1]),L=std::atoi(argv[2]),s=std::atoi(argv[3]),n=P+L;
  auto trials=std::strtoull(argv[4],nullptr,10); rng_state=std::strtoull(argv[5],nullptr,10);
  if(n>7||s>20||n<2) return 2;
  std::array<U,32> vals{};
  std::array<Gate,20> gates{};
  std::array<unsigned,20> cone{};
  for(int i=0;i<n;++i) for(int x=0;x<(1<<n);++x) if((x>>i)&1) vals[i]|=U(1)<<x;
  std::uint64_t quadratic=0,fourfree=0,at_budget=0,distinct=0,nonread2=0,topform=0,local_irred=0;
  std::set<unsigned> graphs;
  for(std::uint64_t trial=0;trial<trials;++trial) {
    for(int j=0;j<s;++j) {
      int k=n+j;
      int a=(j && rng()%10<4) ? k-1 : rng()%k;
      int b=rng()%k;
      if(a==b) b=(b+1)%k;
      if(a>b) std::swap(a,b);
      int op=rng()%2;
      gates[j]={op,a,b};
      vals[k]=op ? vals[a]|vals[b] : vals[a]&vals[b];
      cone[j]=0;
      for(int w:{a,b}) if(w>=n) cone[j]|=(1u<<(w-n))|cone[w-n];
    }
    U f=vals[n+s-1],target=0;
    unsigned E=0;
    for(int p=0;p<P;++p) for(int l=0;l<L;++l) {
      int x=(1<<p)|(1<<(P+l));
      if((f>>x)&1) { E|=1u<<(p*L+l); target|=vals[p]&vals[P+l]; }
    }
    if(!E||target!=f) continue;
    ++quadratic;
    bool ff=true;
    for(int p=0;p<P;++p) for(int q=p+1;q<P;++q) {
      unsigned a=(E>>(p*L))&((1u<<L)-1),b=(E>>(q*L))&((1u<<L)-1);
      if(__builtin_popcount(a&b)>=2) ff=false;
    }
    if(!ff) continue;
    ++fourfree;
    unsigned live=cone[s-1]|(1u<<(s-1));
    int size=__builtin_popcount(live);
    int tau=n;
    for(int v=0;v<(1<<n);++v) {
      if(__builtin_popcount(unsigned(v))>=tau) continue;
      bool cover=true;
      for(int p=0;p<P;++p) for(int l=0;l<L;++l)
        if(((E>>(p*L+l))&1)&&!((v>>p)&1)&&!((v>>(P+l))&1)) cover=false;
      if(cover) tau=__builtin_popcount(unsigned(v));
    }
    int budget=__builtin_popcount(E)+tau-1;
    if(size>budget) continue;
    ++at_budget; graphs.insert(E);
    bool dup=false;
    for(int j=0;j<s;++j) if((live>>j)&1)
      for(int i=0;i<n+j;++i) if(i<n||((live>>(i-n))&1)) if(vals[i]==vals[n+j]) dup=true;
    if(dup) continue;
    ++distinct;
    bool bad=false;
    for(int p=0;p<P&&!bad;++p) for(int l=0;l<L&&!bad;++l) if((E>>(p*L+l))&1) {
      std::array<unsigned,32> v{}; v[p]=1u<<4; v[P+l]=1u<<1;
      for(int j=0;j<s;++j) {
        auto g=gates[j]; v[n+j]=g.op ? v[g.a]|v[g.b] : capsum(v[g.a],v[g.b]);
      }
      if(!(v[n+s-1]&((1u<<5)|(1u<<6)|(1u<<9)|(1u<<10)))) bad=true;
    }
    if(!bad) continue;
    ++nonread2;
    std::array<bool,20> dirty{};
    std::array<int,20> users{};
    bool tf=true;
    for(int j=0;j<s;++j) if((live>>j)&1) {
      auto g=gates[j]; dirty[j]=!g.op&&bool(vals[n+j]&~f);
      for(int w:{g.a,g.b}) if(w>=n) ++users[w-n];
      if(!g.op) for(int i=0;i<j;++i) if((cone[j]>>i)&1) if(!gates[i].op&&!dirty[i]) tf=false;
    }
    if(!tf) continue;
    ++topform;
    bool reducible=false;
    for(int j=0;j<s;++j) if((live>>j)&1) {
      auto g=gates[j];
      for(auto pair:{std::pair<int,int>{g.a,g.b},{g.b,g.a}}) {
        int child=pair.first,other=pair.second;
        if(child<n||users[child-n]!=1||gates[child-n].op!=g.op) continue;
        auto h=gates[child-n];
        for(int w:{h.a,h.b}) {
          U value=g.op ? vals[w]|vals[other] : vals[w]&vals[other];
          if(value==vals[n+j]) reducible=true;
        }
      }
    }
    if(reducible) continue;
    ++local_irred;
    std::cout<<"FOUND trial="<<trial<<" edges="<<E<<" live_size="<<size<<" star_budget="<<budget<<" live_mask="<<live<<" gates=";
    for(int j=0;j<s;++j) std::cout<<'['<<gates[j].op<<','<<gates[j].a<<','<<gates[j].b<<']';
    std::cout<<'\n'<<std::flush;
  }
  std::cout<<"trials="<<trials<<" quadratic="<<quadratic<<" four_free="<<fourfree<<" at_star_budget="<<at_budget<<" at_budget_distinct="<<distinct<<" distinct_graphs="<<graphs.size()<<" nonread2="<<nonread2<<" nonread2_topform="<<topform<<" local_irred="<<local_irred<<'\n';
}
