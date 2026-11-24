#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <vector>
using U=unsigned __int128;
struct Graph { unsigned edges; U table; };
int main(int argc,char**argv) {
  if(argc!=3) { std::cerr<<"usage: four_clause_blocks P L\n"; return 2; }
  int P=std::atoi(argv[1]),L=std::atoi(argv[2]),n=P+L;
  if(n>7||P<1||L<1) return 2;
  std::array<U,7> input{};
  for(int i=0;i<n;++i) for(int x=0;x<(1<<n);++x) if((x>>i)&1) input[i]|=U(1)<<x;
  std::vector<Graph> graphs;
  for(unsigned e=1;e<(1u<<(P*L));e+=2) {
    bool ff=true;
    for(int p=0;p<P;++p) for(int q=p+1;q<P;++q) {
      unsigned a=(e>>(p*L))&((1u<<L)-1),b=(e>>(q*L))&((1u<<L)-1);
      if(__builtin_popcount(a&b)>1) ff=false;
    }
    if(!ff) continue;
    U f=0;
    for(int p=0;p<P;++p) for(int l=0;l<L;++l) if((e>>(p*L+l))&1) f|=input[p]&input[P+l];
    graphs.push_back({e,f});
  }
  std::uint64_t sig_count=1;
  for(int i=0;i<n-2;++i) sig_count*=8;
  std::uint64_t below=0,star=0,double_star=0,bad=0,center_fail=0;
  std::array<unsigned,7> sig{};
  sig[0]=7; sig[P]=8;
  for(std::uint64_t code=0;code<sig_count;++code) {
    auto digits=code;
    for(int i=0;i<n;++i) if(i!=0&&i!=P) {
      unsigned a=digits%8; digits/=8;
      sig[i]=i<P ? a : ((a&3)|((a&4)<<1));
    }
    std::array<U,4> clause{};
    for(int i=0;i<n;++i) for(int j=0;j<4;++j) if((sig[i]>>j)&1) clause[j]|=input[i];
    U block=clause[0]&clause[1]&clause[2]&clause[3];
    unsigned block_edges=0,off_lines=0,all_lines=0,center_lines=0;
    for(int p=0;p<P;++p) for(int l=0;l<L;++l) if((sig[p]|sig[P+l])==15) {
      block_edges|=1u<<(p*L+l);
      all_lines|=1u<<l;
      if(p) off_lines|=1u<<l; else center_lines|=1u<<l;
    }
    for(auto g:graphs) if(!(block&~g.table)) {
      ++below;
      if(all_lines&~center_lines) ++center_fail;
      if(__builtin_popcount(off_lines)>1) {
        ++bad;
        std::cout<<"COUNTEREXAMPLE target_edges="<<g.edges<<" block_edges="<<block_edges<<" sig=";
        for(int i=0;i<n;++i) std::cout<<sig[i]<<',';
        std::cout<<'\n';
      } else if(off_lines) ++double_star; else ++star;
    }
  }
  std::cout<<"P="<<P<<" L="<<L<<" normalized_signature_assignments="<<sig_count<<" C4free_graphs_with_bad_edge="<<graphs.size()<<" below_target_cases="<<below<<" pure_center_stars="<<star<<" off_center_cases="<<double_star<<" double_star_violations="<<bad<<" center_all_lines_violations="<<center_fail<<'\n';
  std::cout<<"Normalization: distinguished point signature7, distinguished line8; last clause contains no points; clause bit2 contains no lines. Every below-target four-clause block with a forced3+1 bad edge admits this normalization by permuting its first three clauses. Exact truth tables use all2^(P+L) assignments.\n";
}
