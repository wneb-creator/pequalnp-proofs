#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <unordered_map>
#include <vector>

using U = std::uint64_t;
struct Target { unsigned edge_mask; int predicted; int observed = 99; bool four_free; bool bad_minimum = false; std::uint64_t checked_minima = 0; };
int P, L, n, depth_max;
std::unordered_map<U, Target> targets;
std::array<U, 20> wire;
std::array<std::uint64_t, 10> count{};
std::array<std::array<int,3>,10> circuit;
std::uint64_t minima_with_dirty_and=0;
std::uint64_t minima_topform_two_dirty_cone=0;

unsigned cap_sum(unsigned A, unsigned B) {
  unsigned out=0;
  for(unsigned i=0;i<16;++i) if((A>>i)&1) for(unsigned j=0;j<16;++j) if((B>>j)&1)
    out |= 1u << (4*std::min(3u,(i>>2)+(j>>2))+std::min(3u,(i&3)+(j&3)));
  return out;
}

void check_minimum(Target &t, int depth) {
  if(!t.four_free || depth!=t.predicted) return;
  ++t.checked_minima;
  U target=wire[n+depth-1];
  std::array<unsigned,10> ancestors{};
  std::array<bool,10> dirty{};
  bool topform=true, two_dirty_cone=false, any_dirty=false;
  for(int j=0;j<depth;++j) {
    for(int a=1;a<=2;++a) {
      int w=circuit[j][a];
      if(w>=n) ancestors[j]|=(1u<<(w-n))|ancestors[w-n];
    }
    dirty[j]=!circuit[j][0] && bool(wire[n+j]&~target);
    any_dirty|=dirty[j];
    if(!circuit[j][0]) {
      int nd=0;
      for(int i=0;i<j;++i) if((ancestors[j]>>i)&1) {
        nd+=dirty[i];
        if(!circuit[i][0] && !dirty[i]) topform=false;
      }
      if(!dirty[j] && nd>=2) two_dirty_cone=true;
    }
  }
  minima_with_dirty_and+=any_dirty;
  minima_topform_two_dirty_cone+=topform&&two_dirty_cone;
  if(t.bad_minimum) return;
  for(int p=0;p<P;++p) for(int l=0;l<L;++l) if((t.edge_mask>>(p*L+l))&1) {
    std::array<unsigned,20> V{};
    V[p]=1u<<4;
    V[P+l]=1u<<1;
    for(int j=0;j<depth;++j) {
      auto g=circuit[j];
      V[n+j]=g[0] ? V[g[1]]|V[g[2]] : cap_sum(V[g[1]],V[g[2]]);
    }
    unsigned good=(1u<<5)|(1u<<6)|(1u<<9)|(1u<<10);
    if(!(V[n+depth-1]&good)) {
      t.bad_minimum=true;
      std::cout<<"OPTIMAL_NONREAD2 edge_mask="<<t.edge_mask<<" depth="<<depth<<" edge="<<p<<','<<l<<" gates=";
      for(int j=0;j<depth;++j) std::cout<<'['<<circuit[j][0]<<','<<circuit[j][1]<<','<<circuit[j][2]<<']';
      std::cout<<'\n';
      return;
    }
  }
}

void search(int depth) {
  if (depth == depth_max) return;
  const int k = n + depth;
  for (int a = 0; a < k; ++a) for (int b = a+1; b < k; ++b) {
    for (int op = 0; op < 2; ++op) {
      U f = op ? wire[a] | wire[b] : wire[a] & wire[b];
      bool duplicate = false;
      for (int i = 0; i < k; ++i) if (wire[i] == f) { duplicate = true; break; }
      if (duplicate) continue;
      ++count[depth+1];
      circuit[depth]={op,a,b};
      wire[k] = f;
      auto it = targets.find(f);
      if (it != targets.end()) {
        it->second.observed = std::min(it->second.observed, depth+1);
        check_minimum(it->second, depth+1);
      }
      search(depth+1);
    }
  }
}

int main(int argc, char **argv) {
  if (argc != 4) { std::cerr << "usage: exhaust_small P L depth\n"; return 2; }
  P = std::stoi(argv[1]); L = std::stoi(argv[2]); depth_max = std::stoi(argv[3]); n=P+L;
  if (n > 6 || P*L >= 31 || depth_max > 8) return 2;
  for (int i=0; i<n; ++i) for (unsigned x=0; x<(1u<<n); ++x)
    if ((x>>i)&1) wire[i] |= U(1)<<x;
  int graphs=0;
  for (unsigned e=0; e<(1u<<(P*L)); ++e) {
    bool ff=true;
    for (int p=0;p<P;++p) for(int q=p+1;q<P;++q)
      for(int l=0;l<L;++l) for(int m=l+1;m<L;++m)
        if (((e>>(p*L+l))&1)&&((e>>(p*L+m))&1)&&((e>>(q*L+l))&1)&&((e>>(q*L+m))&1)) ff=false;
    int tau=n;
    for (unsigned s=0;s<(1u<<n);++s) {
      bool covers=true;
      for(int p=0;p<P;++p) for(int l=0;l<L;++l)
        if (((e>>(p*L+l))&1) && !((s>>p)&1) && !((s>>(P+l))&1)) covers=false;
      if(covers) tau=std::min(tau,__builtin_popcount(s));
    }
    U f=0;
    for(int p=0;p<P;++p) for(int l=0;l<L;++l)
      if((e>>(p*L+l))&1) f |= wire[p]&wire[P+l];
    targets.emplace(f,Target{e,e ? __builtin_popcount(e)+tau-1 : 0,e ? 99 : 0,ff});
    if(ff) ++graphs;
  }
  search(0);
  int verified=0,under=0,pending=0,bad=0;
  std::uint64_t checked_minima=0;
  for (const auto &[f,t]:targets) if(t.four_free) {
    bad+=t.bad_minimum;
    checked_minima+=t.checked_minima;
    if(t.observed<t.predicted) {
      ++under; std::cout << "COUNTEREXAMPLE edge_mask=" << t.edge_mask << " star_bound=" << t.predicted << " observed=" << t.observed << '\n';
    } else if(t.predicted<=depth_max+1) ++verified;
    else ++pending;
  }
  std::cout << "P="<<P<<" L="<<L<<" max_depth="<<depth_max<<" four_cycle_free_graphs="<<graphs<<" lower_bound_verified="<<verified<<" counterexamples="<<under<<" insufficient_depth="<<pending<<'\n';
  std::cout << "star_bound_size_circuits_checked_for_read2="<<checked_minima<<" graphs_with_nonread2_at_star_bound="<<bad<<'\n';
  std::cout << "minimum_circuits_with_dirty_and="<<minima_with_dirty_and<<" minimum_topform_circuits_with_two_dirty_in_one_top_cone="<<minima_topform_two_dirty_cone<<'\n';
  for(int d=1;d<=depth_max;++d) std::cout << "sequences_depth_"<<d<<'='<<count[d]<<'\n';
  std::cout << "Method: all commutative fan-in-two AND/OR straight-line programs through depth, omitting gates semantically equal to earlier wires (eliminable in any minimum circuit). Missing output realizes false at zero gates. The bound is |E| + minimum vertex-cover size - 1 for nonempty graphs. A verified case has no smaller circuit; this executable does not formalize the bound in Lean.\n";
}
