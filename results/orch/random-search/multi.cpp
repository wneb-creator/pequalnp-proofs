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
#ifndef N
#define N 8
#endif
using U=uint64_t;
constexpr int n=N,np=n*(n-1)/2,nw=1<<(n-6);
struct Bits {std::array<U,nw> b{};bool operator==(const Bits&)const=default;};
struct Node {Bits table;U used;int a,b,op;};
struct Target{int edges,tau;};
int main(int argc,char**argv){
 long long rounds=argc>1?atoll(argv[1]):100000000LL;
 int seed=argc>2?atoi(argv[2]):1;
 std::mt19937_64 rng(seed);std::array<Bits,n> input{};
 std::array<std::pair<int,int>,np> pairs;std::array<Bits,np> pairtable;
 int q=0;for(int a=0;a<n;a++)for(int b=a+1;b<n;b++)pairs[q++]={a,b};
 for(int i=0;i<n;i++)for(int x=0;x<(1<<n);x++)if(x>>i&1)input[i].b[x>>6]|=U(1)<<(x&63);
 for(int k=0;k<np;k++){auto[a,b]=pairs[k];for(int w=0;w<nw;w++)pairtable[k].b[w]=input[a].b[w]&input[b].b[w];}
 std::unordered_map<U,Target> targets;
 std::cout<<"n "<<n<<" seed "<<seed<<" rounds "<<rounds<<std::endl;
 std::array<Node,80> nodes;
 for(int i=0;i<n;i++)nodes[i]={input[i],0,-1,-1,-1};
 long long hits=0,equalities=0;int largestEquality=0;U maxgraph=0;
 auto start=std::chrono::steady_clock::now();
 for(long long trial=0;trial<rounds;trial++){
  const int len=12+rng()%39;
  for(int j=0;j<len;j++){
   int k=n+j;int a=(j>0 && rng()%3==0)?k-1:rng()%k;int b=rng()%k;
   int op=rng()%3!=0;Bits v;
   for(int w=0;w<nw;w++)v.b[w]=op?(nodes[a].table.b[w]|nodes[b].table.b[w]):(nodes[a].table.b[w]&nodes[b].table.b[w]);
   if(v==nodes[a].table || v==nodes[b].table){j--;if(rng()%10==0)break;continue;}
   nodes[k]={v,nodes[a].used|nodes[b].used|(U(1)<<j),a,b,op};
   bool pure=true;
   for(int i=0;i<n;i++){int x=1<<i;if(v.b[x>>6]>>(x&63)&1)pure=false;}
   if(!pure)continue;
   std::array<unsigned,n>adj{};Bits expected;U graph=0;int ne=0;
   for(int z=0;z<np;z++){
    auto[c,d]=pairs[z];int x=(1<<c)|(1<<d);
    if(v.b[x>>6]>>(x&63)&1){graph|=U(1)<<z;ne++;adj[c]|=1u<<d;adj[d]|=1u<<c;for(int w=0;w<nw;w++)expected.b[w]|=pairtable[z].b[w];}
   }
   if(!ne || !(expected==v))continue;
   for(int c=0;c<n;c++)for(int d=c+1;d<n;d++)if(std::popcount(adj[c]&adj[d])>=2)pure=false;
   if(!pure)continue;
   int tau;auto it=targets.find(graph);
   if(it!=targets.end())tau=it->second.tau;
   else {
    tau=n;for(unsigned s=0;s<(1u<<n);s++){
     if(std::popcount(s)>=tau)continue;bool cov=true;
     for(int i=0;i<n;i++)if(!(s>>i&1)&&(adj[i]&~s)){cov=false;break;}
     if(cov)tau=std::popcount(s);
    }
    targets.emplace(graph,Target{ne,tau});
   }
   hits++;int cost=std::popcount(nodes[k].used);int bound=ne+tau-1;
   if(cost==bound){equalities++;if(bound>largestEquality){largestEquality=bound;maxgraph=graph;std::cout<<"new equality "<<bound<<" edges "<<ne<<" tau "<<tau<<" graph "<<graph<<" trial "<<trial<<std::endl;}}
   if(cost<bound){
    std::cout<<"COUNTEREXAMPLE cost "<<cost<<" edges "<<ne<<" tau "<<tau<<" graph "<<graph<<" trial "<<trial<<" output "<<k<<std::endl;
    for(int z=n;z<=k;z++)std::cout<<z<<" "<<(nodes[z].op?"or":"and")<<" "<<nodes[z].a<<" "<<nodes[z].b<<" used "<<((nodes[k].used>>(z-n))&1)<<std::endl;
    return 0;
   }
  }
  if(trial && trial%1000000==0)std::cout<<"progress "<<trial<<" hits "<<hits<<" equalities "<<equalities<<" graphs "<<targets.size()<<" seconds "<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<std::endl;
 }
 std::cout<<"DONE rounds "<<rounds<<" hits "<<hits<<" equalities "<<equalities<<" largestEquality "<<largestEquality<<" graph "<<maxgraph<<" graphs "<<targets.size()<<" seconds "<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<std::endl;
}
