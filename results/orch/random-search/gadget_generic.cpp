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
#define N 7
#endif
using U=uint64_t;constexpr int n=N,np=n*(n-1)/2,nw=1<<(n-6);static_assert(n>=6&&n<=11);
struct Bits{std::array<U,nw>b{};bool operator==(const Bits&)const=default;};
struct Target{int edges,tau;U graph;Bits safe;};
struct Node{Bits table;U used;int a,b,op,support;U graph;};
int main(int argc,char**argv){
 long long rounds=argc>1?atoll(argv[1]):1000000LL;int seed=argc>2?atoi(argv[2]):2028;double limit=argc>3?atof(argv[3]):0;int mode=argc>4?atoi(argv[4]):0;std::mt19937_64 rng(seed);
 std::array<Bits,n>input{};std::array<std::pair<int,int>,np>pairs;std::array<Bits,1<<n>ors{};std::array<Bits,np>pairtables;
 int q=0;for(int a=0;a<n;a++)for(int b=a+1;b<n;b++)pairs[q++]={a,b};
 for(int i=0;i<n;i++)for(int x=0;x<(1<<n);x++)if(x>>i&1)input[i].b[x>>6]|=U(1)<<(x&63);
 for(int s=0;s<(1<<n);s++)for(int i=0;i<n;i++)if(s>>i&1)for(int w=0;w<nw;w++)ors[s].b[w]|=input[i].b[w];
 for(int z=0;z<np;z++){auto[a,b]=pairs[z];for(int w=0;w<nw;w++)pairtables[z].b[w]=input[a].b[w]&input[b].b[w];}
 std::unordered_map<U,Target>targets;
 auto classify=[&](const Bits&v)->U{
  U g=0;Bits expected;
  for(int i=0;i<n;i++){int x=1<<i;if(v.b[x>>6]>>(x&63)&1)return 0;}
  for(int z=0;z<np;z++){auto[a,b]=pairs[z];int x=(1<<a)|(1<<b);if(v.b[x>>6]>>(x&63)&1){g|=U(1)<<z;for(int w=0;w<nw;w++)expected.b[w]|=pairtables[z].b[w];}}
  if(!g||!(v==expected))return 0;
  if(targets.count(g))return g;
  std::array<unsigned,n>adj{};for(int z=0;z<np;z++)if(g>>z&1){auto[a,b]=pairs[z];adj[a]|=1u<<b;adj[b]|=1u<<a;}
  U commonPairs=0;for(int z=0;z<np;z++){auto[a,b]=pairs[z];int c=std::popcount(adj[a]&adj[b]);if(c>=2)return 0;if(c)commonPairs|=U(1)<<z;}
  int tau=n;for(unsigned s=0;s<(1u<<n);s++){if(std::popcount(s)>=tau)continue;bool cov=true;for(int i=0;i<n;i++)if(!(s>>i&1)&&(adj[i]&~s)){cov=false;break;}if(cov)tau=std::popcount(s);}
  Bits safe;for(unsigned s=0;s<(1u<<n);s++)if(std::popcount(s)>=2){bool yes=true;for(int z=0;z<np;z++)if(commonPairs>>z&1){auto[a,b]=pairs[z];if((s>>a&1)&&(s>>b&1)){yes=false;break;}}if(yes)safe.b[s>>6]|=U(1)<<(s&63);}
  targets.emplace(g,Target{std::popcount(g),tau,g,safe});return g;
 };
 std::array<Node,80>nodes;for(int i=0;i<n;i++)nodes[i]={input[i],0,-1,-1,-1,1<<i,0};
 std::cout<<"gadget generic n "<<n<<" seed "<<seed<<" mode "<<mode<<" rounds "<<rounds<<std::endl;
 long long outputs=0,safeAux=0,packTests=0,completed=0;int bestGain=-100;auto start=std::chrono::steady_clock::now();
 for(long long trial=0;trial<rounds;trial++){
  int want=12+rng()%39,k=n;
  for(int tries=0;tries<160 && k<n+want;tries++){
   int a=(k>n&&rng()%3==0)?k-1:rng()%k,b=rng()%k,op=mode?(rng()%3!=0):(rng()%2);Bits v;
   for(int w=0;w<nw;w++)v.b[w]=op?(nodes[a].table.b[w]|nodes[b].table.b[w]):(nodes[a].table.b[w]&nodes[b].table.b[w]);
   if(v==nodes[a].table||v==nodes[b].table)continue;
   int s=0;for(int i=0;i<n;i++){int x=1<<i;if(v.b[x>>6]>>(x&63)&1)s|=1<<i;}if(!(v==ors[s])||std::popcount(unsigned(s))<2)s=-1;
   nodes[k]={v,nodes[a].used|nodes[b].used|(U(1)<<(k-n)),a,b,op,s,classify(v)};k++;
  }
  for(int out=n;out<k;out++){
   if(!nodes[out].graph)continue;outputs++;const Target&t=targets.at(nodes[out].graph);int bound=t.edges+t.tau-1;
   auto check=[&](const std::vector<int>&sel)->bool{
    U used=nodes[out].used;int weight=0;for(int j:sel){used|=nodes[j].used;weight+=std::popcount(unsigned(nodes[j].support))-1;}
    int gain=bound+weight-std::popcount(used);packTests++;bestGain=std::max(bestGain,gain);if(gain<=0)return false;
    std::cout<<"GADGET WITNESS n "<<n<<" gain "<<gain<<" graph "<<t.graph<<" edges "<<t.edges<<" tau "<<t.tau<<" output "<<out<<" livecost "<<std::popcount(used)<<" auxcount "<<sel.size()<<" trial "<<trial<<std::endl;
    for(int j:sel)std::cout<<"aux "<<j<<" support "<<nodes[j].support<<std::endl;
    for(int j=n;j<k;j++)std::cout<<j<<" "<<(nodes[j].op?"or":"and")<<" "<<nodes[j].a<<" "<<nodes[j].b<<" used "<<((used>>(j-n))&1)<<std::endl;return true;
   };
   if(check({}))return 0;
   std::vector<int>aux;for(int j=n;j<k;j++)if(nodes[j].support>=0){int s=nodes[j].support;if(t.safe.b[s>>6]>>(s&63)&1){aux.push_back(j);safeAux++;}}
   auto compat=[&](int a,int b){return std::popcount(unsigned(nodes[a].support&nodes[b].support))<=1;};
   for(int a=0;a<(int)aux.size();a++){
    if(check({aux[a]}))return 0;
    for(int b=0;b<a;b++)if(compat(aux[a],aux[b])){if(check({aux[a],aux[b]}))return 0;for(int c=0;c<b;c++)if(compat(aux[a],aux[c])&&compat(aux[b],aux[c]))if(check({aux[a],aux[b],aux[c]}))return 0;}
   }
   std::vector<int>selected;U used=nodes[out].used;
   for(int step=0;step<6;step++){
    int choose=-1,best=-100;for(int a:aux){bool ok=true;for(int b:selected)if(!compat(a,b))ok=false;if(!ok)continue;int profit=std::popcount(unsigned(nodes[a].support))-1-std::popcount(nodes[a].used&~used);if(profit>best){best=profit;choose=a;}}
    if(choose<0||best<0)break;selected.push_back(choose);used|=nodes[choose].used;if(check(selected))return 0;
   }
  }
  completed=trial+1;
  if(limit>0 && trial%10000==0 && std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()>=limit){std::cout<<"TIME_LIMIT"<<std::endl;break;}
  if(trial&&trial%100000==0)std::cout<<"progress "<<trial<<" outputs "<<outputs<<" safeaux "<<safeAux<<" packs "<<packTests<<" graphs "<<targets.size()<<" bestgain "<<bestGain<<" seconds "<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<std::endl;
 }
 std::cout<<"DONE rounds "<<completed<<" outputs "<<outputs<<" safeaux "<<safeAux<<" packs "<<packTests<<" graphs "<<targets.size()<<" bestgain "<<bestGain<<" seconds "<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<std::endl;
}
