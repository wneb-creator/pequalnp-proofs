#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <set>
#include <utility>
#include <vector>
using namespace std;
struct Gate {int op,a,b; uint64_t value;};
int main() {
  auto start=chrono::steady_clock::now();
  array<uint64_t,6> raw{};
  for(int x=0;x<64;x++)for(int i=0;i<6;i++)if(x>>i&1)raw[i]|=uint64_t(1)<<x;
  const int vertex[6]={0,2,3,5,6,9};
  const int stars[4][3]={{0,2,5},{0,1,4},{2,3,4},{1,3,5}};
  const int matching[3][2]={{0,3},{1,2},{4,5}};
  vector<uint64_t> base(raw.begin(),raw.end());set<pair<int,int>> pairset;
  array<uint64_t,4> sv{};
  for(int s=0;s<4;s++) {
    for(int i=0;i<3;i++)sv[s]|=raw[stars[s][i]];
    for(int i=0;i<3;i++)for(int j=i+1;j<3;j++)pairset.insert(minmax(stars[s][i],stars[s][j]));
  }
  for(auto [a,b]:pairset)base.push_back(raw[a]|raw[b]);
  for(auto v:sv)base.push_back(v);
  uint64_t goal=0;for(auto e:matching)goal|=raw[e[0]]&raw[e[1]];
  uint64_t tested=0,solutions=0;
  for(int bop=0;bop<2;bop++)for(auto e:matching) {
    auto bank=base;bank.push_back(bop?(raw[e[0]]|raw[e[1]]):(raw[e[0]]&raw[e[1]]));
    vector<Gate> first;
    for(int a=0;a<(int)bank.size();a++) {
      first.push_back({2,a,0,~bank[a]});
      for(int b=a;b<(int)bank.size();b++) {
        first.push_back({0,a,b,bank[a]&bank[b]});
        first.push_back({1,a,b,bank[a]|bank[b]});
      }
    }
    for(int s=0;s<4;s++) {
      int best=65;uint64_t count=0;
      for(auto g:first) {
        auto v=bank;v.push_back(g.value);
        for(int a=0;a<(int)v.size();a++) {
          int err=__builtin_popcountll((sv[s]&~v[a])^goal);tested++;
          best=min(best,err);if(!err)count++;
          for(int b=a;b<(int)v.size();b++)for(int op=0;op<2;op++) {
            uint64_t val=op?(v[a]|v[b]):(v[a]&v[b]);
            err=__builtin_popcountll((sv[s]&val)^goal);tested++;
            best=min(best,err);if(!err)count++;
          }
        }
      }
      solutions+=count;
      cout<<"bank_op "<<bop<<" edge "<<vertex[e[0]]<<' '<<vertex[e[1]]<<" factored_star "<<s<<" best_errors "<<best<<" solutions "<<count<<'\n';
    }
  }
  cout<<"all_pair_ORs "<<pairset.size()<<" base_functions "<<base.size()<<" tested "<<tested<<" solutions "<<solutions<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<'\n';
  return solutions?2:0;
}
