#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

struct Signal { uint64_t f; unsigned color; };
struct Gate { int a, b; bool is_or; };
struct Target { unsigned edges; int lower; };
int p, l, n, maxdepth;
std::vector<Signal> wires;
std::vector<Gate> gates;
std::unordered_map<uint64_t,Target> targets;
uint64_t visited[12]{};
bool witness=false;
bool low_or=false,low_and=false;
struct Symmetry { uint64_t table[8][256]{}; bool swap; };
std::vector<Symmetry> symmetries;
std::unordered_set<std::string> seen[4];

std::string canonical() {
  std::vector<std::pair<uint64_t,unsigned>> best;
  bool first=true;
  for(const auto& sym:symmetries) {
    std::vector<std::pair<uint64_t,unsigned>> transformed;
    for(size_t j=n;j<wires.size();++j) {
      uint64_t f=0;
      for(int k=0;k<8;++k) f|=sym.table[k][(wires[j].f>>(8*k))&255];
      unsigned color=wires[j].color;
      if(sym.swap) color=((color&1)<<1)|((color&2)>>1);
      transformed.emplace_back(f,color);
    }
    std::sort(transformed.begin(),transformed.end());
    if(first||transformed<best) { best=std::move(transformed); first=false; }
  }
  std::string result;
  for(auto [f,c]:best) {
    for(int k=0;k<8;++k) result.push_back(char((f>>(8*k))&255));
    result.push_back(char(c));
  }
  int or_count=0;
  for(auto g:gates) or_count+=g.is_or;
  result.push_back(char(or_count));
  return result;
}

void search(int depth) {
  ++visited[depth];
  if (depth == maxdepth) return;
  if(depth<=3 && !seen[depth].insert(canonical()).second) return;
  const int count=wires.size();
  for(int a=0;a<count;++a) for(int b=a;b<count;++b) for(int op=0;op<2;++op) {
    unsigned col=op ? (wires[a].color|wires[b].color) : 0;
    if(col==3) continue;
    uint64_t f=op ? (wires[a].f|wires[b].f) : (wires[a].f&wires[b].f);
    bool dominated=false;
    for(const auto& s:wires) if(s.f==f && (s.color&col)==s.color) { dominated=true; break; }
    if(dominated) continue;
    gates.push_back({a,b,bool(op)});
    auto t=targets.find(f);
    if(t!=targets.end()) {
      int ors=0;
      for(auto g:gates) ors+=g.is_or;
      int ec=__builtin_popcount(t->second.edges),tau=t->second.lower+1-ec;
      if((!low_or&&ors<ec-1)||(!low_and&&depth+1-ors<tau)) {
        std::cout<<"SEPARATE BOUND FAILURE edges="<<t->second.edges<<" edge_count="<<ec<<" tau="<<tau<<" OR="<<ors<<" AND="<<depth+1-ors<<'\n';
        for(auto g:gates) std::cout<<(g.is_or?"OR ":"AND ")<<g.a<<' '<<g.b<<'\n';
        low_or|=ors<ec-1; low_and|=depth+1-ors<tau; std::cout.flush();
      }
    }
    if(t!=targets.end() && depth+1<t->second.lower) {
      std::cout << "COUNTEREXAMPLE edges=" << t->second.edges << " expected_bound=" << t->second.lower << " gates=" << depth+1 << '\n';
      for(auto g:gates) std::cout << (g.is_or?"OR ":"AND ") << g.a << ' ' << g.b << '\n';
      witness=true; return;
    }
    wires.push_back({f,col});
    search(depth+1);
    if(witness) return;
    wires.pop_back(); gates.pop_back();
  }
}

int main(int argc,char**argv) {
  if(argc!=4) return 2;
  p=std::atoi(argv[1]); l=std::atoi(argv[2]); maxdepth=std::atoi(argv[3]); n=p+l;
  if(n>6 || p*l>24 || maxdepth>10) return 2;
  std::vector<int> ap(p),bp(l);
  std::iota(ap.begin(),ap.end(),0); std::iota(bp.begin(),bp.end(),0);
  do {
    do {
      for(int swap=0;swap<=(p==l);++swap) {
        Symmetry sym{}; sym.swap=swap;
        for(unsigned x=0;x<(1u<<n);++x) {
          unsigned y=0;
          for(int i=0;i<p;++i) if(x&(1u<<i)) y|=1u<<(ap[i]+(swap?p:0));
          for(int i=0;i<l;++i) if(x&(1u<<(p+i))) y|=1u<<(bp[i]+(swap?0:p));
          for(int v=0;v<256;++v) if(v&(1u<<(x%8))) sym.table[x/8][v]|=uint64_t(1)<<y;
        }
        symmetries.push_back(sym);
      }
    } while(std::next_permutation(bp.begin(),bp.end()));
  } while(std::next_permutation(ap.begin(),ap.end()));
  for(unsigned E=1;E<(1u<<(p*l));++E) {
    auto edge=[&](int a,int b) {return bool(E&(1u<<(a*l+b)));};
    bool c4=false;
    for(int a=0;a<p;++a) for(int aa=a+1;aa<p;++aa)
      for(int b=0;b<l;++b) for(int bb=b+1;bb<l;++bb)
        if(edge(a,b)&&edge(a,bb)&&edge(aa,b)&&edge(aa,bb)) c4=true;
    if(c4) continue;
    int cover=n;
    for(unsigned S=0;S<(1u<<n);++S) {
      bool good=true;
      for(int a=0;a<p;++a) for(int b=0;b<l;++b)
        if(edge(a,b)&&!(S&(1u<<a))&&!(S&(1u<<(p+b)))) good=false;
      if(good) cover=std::min(cover,__builtin_popcount(S));
    }
    uint64_t f=0;
    for(unsigned x=0;x<(1u<<n);++x) {
      bool value=false;
      for(int a=0;a<p;++a) for(int b=0;b<l;++b)
        if(edge(a,b)&&(x&(1u<<a))&&(x&(1u<<(p+b)))) value=true;
      if(value) f|=uint64_t(1)<<x;
    }
    targets.emplace(f,Target{E,__builtin_popcount(E)+cover-1});
  }
  for(int i=0;i<n;++i) {
    uint64_t f=0;
    for(unsigned x=0;x<(1u<<n);++x) if(x&(1u<<i)) f|=uint64_t(1)<<x;
    wires.push_back({f,i<p?1u:2u});
  }
  std::cout << "p=" <<p<<" l="<<l<<" maxdepth="<<maxdepth<<" targets="<<targets.size()<<std::endl;
  search(0);
  for(int d=0;d<=maxdepth;++d) std::cout<<"depth "<<d<<" visited "<<visited[d]<<'\n';
  for(int d=0;d<=3;++d) std::cout<<"depth "<<d<<" symmetry classes "<<seen[d].size()<<'\n';
  std::cout<<(witness?"WITNESS":"NO COUNTEREXAMPLE")<<std::endl;
  std::cout<<"Separate bounds violated: OR="<<low_or<<" AND="<<low_and<<std::endl;
  return witness?1:0;
}
