#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <random>
#include <unordered_map>
#include <vector>
using U=uint64_t;
struct Target {int edges,tau;unsigned graph;};
struct Node {U table;unsigned used;int a,b,op;};
int main(int argc,char**argv){
 long long rounds=argc>1?atoll(argv[1]):100000000LL;
 int seed=argc>2?atoi(argv[2]):1;
 std::mt19937_64 rng(seed);
 constexpr int n=6,np=15;
 std::array<U,n> input{};std::array<std::pair<int,int>,np> pairs;
 int q=0;for(int a=0;a<n;a++)for(int b=a+1;b<n;b++)pairs[q++]={a,b};
 for(int i=0;i<n;i++)for(int x=0;x<(1<<n);x++)if(x>>i&1)input[i]|=U(1)<<x;
 std::unordered_map<U,Target> targets;
 for(unsigned g=1;g<(1u<<np);g++){
  std::array<unsigned,n> adj{};int ne=std::popcount(g);
  for(int k=0;k<np;k++)if(g>>k&1){auto[a,b]=pairs[k];adj[a]|=1u<<b;adj[b]|=1u<<a;}
  bool ok=true;for(int a=0;a<n;a++)for(int b=a+1;b<n;b++)if(std::popcount(adj[a]&adj[b])>=2)ok=false;
  if(!ok)continue;
  int tau=n;for(unsigned s=0;s<(1u<<n);s++){
   if(std::popcount(s)>=tau)continue;bool cov=true;
   for(int i=0;i<n;i++)if(!(s>>i&1) && (adj[i]&~s))cov=false;
   if(cov)tau=std::popcount(s);
  }
  U table=0;for(int k=0;k<np;k++)if(g>>k&1){auto[a,b]=pairs[k];table|=input[a]&input[b];}
  targets.emplace(table,Target{ne,tau,g});
 }
 std::cout<<"targets "<<targets.size()<<" seed "<<seed<<" rounds "<<rounds<<std::endl;
 std::array<Node,64> nodes;
 for(int i=0;i<n;i++)nodes[i]={input[i],0,-1,-1,-1};
 long long hits=0,equalities=0;int largestEquality=0;unsigned maxgraph=0;
 auto start=std::chrono::steady_clock::now();
 for(long long trial=0;trial<rounds;trial++){
  const int len=8+rng()%20;
  for(int j=0;j<len;j++){
   int k=n+j;int a=(j>0 && rng()%3==0)?k-1:rng()%k;int b=rng()%k;
   int op=rng()%2;U v=op?(nodes[a].table|nodes[b].table):(nodes[a].table&nodes[b].table);
   if(v==nodes[a].table || v==nodes[b].table){j--;if(rng()%7==0)break;continue;}
   nodes[k]={v,nodes[a].used|nodes[b].used|(1u<<j),a,b,op};
   auto it=targets.find(v);if(it==targets.end())continue;
   hits++;int cost=std::popcount(nodes[k].used);auto t=it->second;int bound=t.edges+t.tau-1;
   if(cost==bound){equalities++;if(bound>largestEquality){largestEquality=bound;maxgraph=t.graph;std::cout<<"new equality "<<bound<<" edges "<<t.edges<<" tau "<<t.tau<<" graph "<<t.graph<<" trial "<<trial<<std::endl;}}
   if(cost<bound){
    std::cout<<"COUNTEREXAMPLE cost "<<cost<<" edges "<<t.edges<<" tau "<<t.tau<<" graph "<<t.graph<<" trial "<<trial<<" output "<<k<<std::endl;
    for(int z=n;z<=k;z++)std::cout<<z<<" "<<(nodes[z].op?"or":"and")<<" "<<nodes[z].a<<" "<<nodes[z].b<<" used "<<((nodes[k].used>>(z-n))&1)<<std::endl;
    return 0;
   }
  }
  if(trial && trial%10000000==0)std::cout<<"progress "<<trial<<" hits "<<hits<<" equalities "<<equalities<<" seconds "<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<std::endl;
 }
 std::cout<<"DONE rounds "<<rounds<<" hits "<<hits<<" equalities "<<equalities<<" largestEquality "<<largestEquality<<" graph "<<maxgraph<<" seconds "<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<std::endl;
}
