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
constexpr int n=6,np=15;
struct Target{int edges,tau;unsigned graph;U safe;};
struct Node{U table;unsigned used;int a,b,op,support;};
int main(int argc,char**argv){
 long long rounds=argc>1?atoll(argv[1]):1000000LL;int seed=argc>2?atoi(argv[2]):2028;double limit=argc>3?atof(argv[3]):0;int mode=argc>4?atoi(argv[4]):0;std::mt19937_64 rng(seed);
 std::array<U,n>input{};std::array<std::pair<int,int>,np>pairs;std::array<U,64>ors{};
 int q=0;for(int a=0;a<n;a++)for(int b=a+1;b<n;b++)pairs[q++]={a,b};
 for(int i=0;i<n;i++)for(int x=0;x<64;x++)if(x>>i&1)input[i]|=U(1)<<x;
 for(int s=0;s<64;s++)for(int i=0;i<n;i++)if(s>>i&1)ors[s]|=input[i];
 std::unordered_map<U,Target>targets;
 for(unsigned g=1;g<(1u<<np);g++){
  std::array<unsigned,n>adj{};for(int k=0;k<np;k++)if(g>>k&1){auto[a,b]=pairs[k];adj[a]|=1u<<b;adj[b]|=1u<<a;}
  bool ok=true;unsigned commonPairs=0;for(int k=0;k<np;k++){auto[a,b]=pairs[k];int c=std::popcount(adj[a]&adj[b]);if(c>=2)ok=false;if(c)commonPairs|=1u<<k;}if(!ok)continue;
  int tau=n;for(unsigned s=0;s<64;s++){if(std::popcount(s)>=tau)continue;bool cov=true;for(int i=0;i<n;i++)if(!(s>>i&1)&&(adj[i]&~s))cov=false;if(cov)tau=std::popcount(s);}
  U safe=0;for(unsigned s=0;s<64;s++)if(std::popcount(s)>=2){bool yes=true;for(int k=0;k<np;k++)if(commonPairs>>k&1){auto[a,b]=pairs[k];if((s>>a&1)&&(s>>b&1))yes=false;}if(yes)safe|=U(1)<<s;}
  U table=0;for(int k=0;k<np;k++)if(g>>k&1){auto[a,b]=pairs[k];table|=input[a]&input[b];}
  targets.emplace(table,Target{std::popcount(g),tau,g,safe});
 }
 std::array<Node,40>nodes;for(int i=0;i<n;i++)nodes[i]={input[i],0,-1,-1,-1,1<<i};
 std::cout<<"gadget search targets "<<targets.size()<<" seed "<<seed<<" rounds "<<rounds<<std::endl;
 long long outputs=0,safeAux=0,packTests=0,completed=0;int bestGain=-100;
 auto start=std::chrono::steady_clock::now();
 for(long long trial=0;trial<rounds;trial++){
  int want=8+rng()%20,k=n;
  for(int tries=0;tries<100 && k<n+want;tries++){
   int a=(k>n&&rng()%3==0)?k-1:rng()%k,b=rng()%k,op=mode?(rng()%3!=0):(rng()%2);U v=op?(nodes[a].table|nodes[b].table):(nodes[a].table&nodes[b].table);
   if(v==nodes[a].table || v==nodes[b].table)continue;
   int s=0;for(int i=0;i<n;i++)if(v>>(1<<i)&1)s|=1<<i;if(v!=ors[s]||std::popcount(unsigned(s))<2)s=-1;
   nodes[k]={v,nodes[a].used|nodes[b].used|(1u<<(k-n)),a,b,op,s};k++;
  }
  for(int out=n;out<k;out++){
   auto it=targets.find(nodes[out].table);if(it==targets.end())continue;outputs++;Target t=it->second;int bound=t.edges+t.tau-1;
   auto check=[&](const std::vector<int>&sel)->bool{
    unsigned used=nodes[out].used;int weight=0;for(int j:sel){used|=nodes[j].used;weight+=std::popcount(unsigned(nodes[j].support))-1;}
    int gain=bound+weight-std::popcount(used);packTests++;bestGain=std::max(bestGain,gain);
    if(gain<=0)return false;
    std::cout<<"GADGET WITNESS gain "<<gain<<" graph "<<t.graph<<" edges "<<t.edges<<" tau "<<t.tau<<" output "<<out<<" livecost "<<std::popcount(used)<<" auxcount "<<sel.size()<<" trial "<<trial<<std::endl;
    for(int j:sel)std::cout<<"aux "<<j<<" support "<<nodes[j].support<<std::endl;
    for(int j=n;j<k;j++)std::cout<<j<<" "<<(nodes[j].op?"or":"and")<<" "<<nodes[j].a<<" "<<nodes[j].b<<" used "<<((used>>(j-n))&1)<<std::endl;
    return true;
   };
   if(check({}))return 0;
   std::vector<int>aux;for(int j=n;j<k;j++)if(nodes[j].support>=0 && (t.safe>>nodes[j].support&1)){aux.push_back(j);safeAux++;}
   auto compat=[&](int a,int b){return std::popcount(unsigned(nodes[a].support&nodes[b].support))<=1;};
   for(int a=0;a<(int)aux.size();a++){
    if(check({aux[a]}))return 0;
    for(int b=0;b<a;b++)if(compat(aux[a],aux[b])){
     if(check({aux[a],aux[b]}))return 0;
     for(int c=0;c<b;c++)if(compat(aux[a],aux[c])&&compat(aux[b],aux[c]))if(check({aux[a],aux[b],aux[c]}))return 0;
    }
   }
   // Greedy larger compatible packs supplement the exhaustive packs of size at most three.
   std::vector<int>selected;unsigned used=nodes[out].used;
   for(int step=0;step<6;step++){
    int choose=-1,best=-100;
    for(int a:aux){bool ok=true;for(int b:selected)if(!compat(a,b))ok=false;if(!ok)continue;int profit=std::popcount(unsigned(nodes[a].support))-1-std::popcount(nodes[a].used&~used);if(profit>best){best=profit;choose=a;}}
    if(choose<0||best<0)break;selected.push_back(choose);used|=nodes[choose].used;if(check(selected))return 0;
   }
  }
  completed=trial+1;
  if(limit>0 && trial%100000==0 && std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()>=limit){std::cout<<"TIME_LIMIT"<<std::endl;break;}
  if(trial&&trial%100000==0)std::cout<<"progress "<<trial<<" outputs "<<outputs<<" safeaux "<<safeAux<<" packs "<<packTests<<" bestgain "<<bestGain<<" seconds "<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<std::endl;
 }
 std::cout<<"DONE rounds "<<completed<<" outputs "<<outputs<<" safeaux "<<safeAux<<" packs "<<packTests<<" bestgain "<<bestGain<<" seconds "<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<std::endl;
}
