#include <array>
#include <bit>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <numeric>
#include <map>
#include <tuple>
#include <vector>
using namespace std;
using Rows = array<uint64_t,8>;
struct Block {uint32_t vertices;uint64_t edges;Rows active;};
vector<Block> blocks;
vector<int> path,best_path;
uint64_t nodes=0,upper_prunes=0,incompatible=0;
array<uint64_t,27> depths{};
int best=0,max_depth=0,max_vertices=0;vector<int> vertex_witness;uint64_t optimum_count=0;map<tuple<int,int,int>,uint64_t> optimum_shapes;vector<int> deepest;
bool timed_out=false;
chrono::steady_clock::time_point began;
double seconds_limit=60;
bool intersects(const Rows& a,const Rows& b){for(int i=0;i<8;i++)if(a[i]&b[i])return true;return false;}
void report_best(uint64_t edges){
 int value=popcount(edges);if(value<=best)return;
 best=value;best_path=path;optimum_count=0;optimum_shapes.clear();
 cout<<"INCUMBENT "<<best<<" BLOCKS";
 for(int i:path)cout<<" "<<blocks[i].vertices;
 cout<<"\n"<<flush;
}
void dfs(const vector<int>& candidates,uint32_t used,uint64_t covered,const Rows& seen,const Rows& saturated){
 ++nodes;++depths[path.size()];if(popcount(used)>max_vertices){max_vertices=popcount(used);vertex_witness=path;}if((int)path.size()>max_depth){max_depth=path.size();deepest=path;}report_best(covered);if(popcount(covered)==best){++optimum_count;++optimum_shapes[{path.size(),popcount(used),popcount(used&8191)}];}
 if((nodes&4095)==0&&chrono::duration<double>(chrono::steady_clock::now()-began).count()>seconds_limit){timed_out=true;return;}
 uint64_t upper=covered;for(int i:candidates)upper|=blocks[i].edges;
 
 for(size_t index=0;index<candidates.size();index++){
  int id=candidates[index];const auto& block=blocks[id];
  Rows next_seen,next_saturated;
  for(int k=0;k<8;k++){next_seen[k]=seen[k]|block.active[k];next_saturated[k]=saturated[k]|(seen[k]&block.active[k]);}
  uint32_t next_used=used|block.vertices;vector<int> next;next.reserve(candidates.size()-index-1);
  for(size_t j=index+1;j<candidates.size();j++){
   int other=candidates[j];
   if((next_used&blocks[other].vertices)||intersects(next_saturated,blocks[other].active)){++incompatible;continue;}
   next.push_back(other);
  }
  path.push_back(id);dfs(next,next_used,covered|block.edges,next_seen,next_saturated);path.pop_back();
  if(timed_out)return;
 }
}
int main(int argc,char**argv){
 if(argc<2)return 2;
 if(argc>2)seconds_limit=stod(argv[2]);
 ifstream in(argv[1]);int nr,ne;in>>nr>>ne;
 if(nr!=468||ne!=52)return 3;
 vector<uint32_t> rows(nr),edges(ne);for(auto& r:rows)in>>r;for(auto& e:edges)in>>e;
 if(!in)return 4;
 auto add=[&](uint32_t mask){
  Block b{mask,0,{}};
  for(int e=0;e<ne;e++)if(mask&edges[e])b.edges|=uint64_t(1)<<e;
  for(int r=0;r<nr;r++)if(mask&rows[r])b.active[r/64]|=uint64_t(1)<<(r%64);
  blocks.push_back(b);
 };
 for(int v=0;v<26;v++)add(uint32_t(1)<<v);
 for(int u=0;u<26;u++)for(int v=u+1;v<26;v++)add((uint32_t(1)<<u)|(uint32_t(1)<<v));
 vector<int> candidates(blocks.size());iota(candidates.begin(),candidates.end(),0);Rows empty{};
 began=chrono::steady_clock::now();dfs(candidates,0,0,empty,empty);
 double elapsed=chrono::duration<double>(chrono::steady_clock::now()-began).count();
 cout<<"RESULT exhaustive="<<(!timed_out)<<" best="<<best<<" elapsed="<<elapsed<<" nodes="<<nodes
     <<" upper_prunes="<<upper_prunes<<" incompatible="<<incompatible<<" max_depth="<<max_depth<<"\n";
 cout<<"BEST_BLOCK_MASKS";for(int i:best_path)cout<<" "<<blocks[i].vertices;cout<<"\n";
 cout<<"MAX_VERTICES "<<max_vertices<<" BLOCKS";for(int i:vertex_witness)cout<<" "<<blocks[i].vertices;cout<<"\n";cout<<"OPTIMUM_COUNT "<<optimum_count<<"\n";for(auto [shape,count]:optimum_shapes){auto [nb,nv,np]=shape;cout<<"OPTIMUM_SHAPE "<<nb<<" "<<nv<<" "<<np<<" "<<count<<"\n";}cout<<"DEEPEST_BLOCK_MASKS";for(int i:deepest)cout<<" "<<blocks[i].vertices;cout<<"\n";for(int d=0;d<=max_depth;d++)cout<<"DEPTH "<<d<<" "<<depths[d]<<"\n";
 return timed_out?1:0;
}
