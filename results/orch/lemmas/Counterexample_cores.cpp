#include <array>
#include <bit>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <utility>
#include <vector>
#include <cstdlib>
int n;std::vector<std::pair<int,int>> es;std::array<unsigned,16> adj{};
uint64_t nodes=0,graphs=0,cores=0;std::array<uint64_t,128> hist{};
void visit(int p,int edges){
 ++nodes;
 if(p==(int)es.size()){
  ++graphs;++hist[edges];unsigned active=(1u<<n)-1;bool changed=true;
  while(changed){changed=false;for(int u=0;u<n;++u)if((active>>u&1)&&std::popcount(adj[u]&active)<3){active&=~(1u<<u);changed=true;}}
  if(active){++cores;std::cout<<"nonempty core found graph="<<graphs<<" active="<<active<<"\n";}
  return;
 }
 visit(p+1,edges);
 auto[u,v]=es[p];
 if(adj[u]&adj[v])return;
 unsigned nu=adj[u];
 while(nu){int x=std::countr_zero(nu);nu&=nu-1;if(adj[x]&adj[v])return;}
 adj[u]|=1u<<v;adj[v]|=1u<<u;
 visit(p+1,edges+1);
 adj[u]&=~(1u<<v);adj[v]&=~(1u<<u);
}
int main(int argc,char**argv){n=std::atoi(argv[1]);if(n<0||n>10)return 1;for(int u=0;u<n;++u)for(int v=u+1;v<n;++v)es.emplace_back(u,v);auto t=std::chrono::steady_clock::now();visit(0,0);std::cout<<"n="<<n<<" graphs="<<graphs<<" nonempty_3cores="<<cores<<" recursion_nodes="<<nodes<<" seconds="<<std::chrono::duration<double>(std::chrono::steady_clock::now()-t).count()<<"\n";for(int m=0;m<128;++m)if(hist[m])std::cout<<"edges="<<m<<" graphs="<<hist[m]<<"\n";}
