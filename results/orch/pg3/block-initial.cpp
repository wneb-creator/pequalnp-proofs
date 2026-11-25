#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <unordered_map>
#include <vector>
constexpr int N=13, INPUTS=26, MAXG=64, TESTS=756, WORDS=12;
constexpr uint64_t POS=(uint64_t(1)<<52)-1;
struct Gate {int a,b;bool is_and;};
using Net=std::array<Gate,MAXG>;
using Sig=std::array<uint64_t,WORDS>;
using Values=std::array<Sig,INPUTS+MAXG>;
uint64_t rngstate;uint64_t rnd(){rngstate^=rngstate<<13;rngstate^=rngstate>>7;return rngstate^=rngstate<<17;}int ri(int n){return rnd()%n;}
Values base{};
std::array<std::pair<int,int>,52>edges;
std::unordered_map<uint64_t,int>matching_cache;
uint64_t matching_calls=0,matching_misses=0;
int count;
int matching(uint64_t removed){
 ++matching_calls;auto it=matching_cache.find(removed);if(it!=matching_cache.end())return it->second;
 ++matching_misses;std::array<uint16_t,N>adj{};
 for(int j=0;j<52;++j)if(!(removed>>j&1)){auto[p,l]=edges[j];adj[p]|=1<<l;}
 std::array<int,N>match;match.fill(-1);int total=0;
 auto augment=[&](auto&&self,int p,uint16_t&seen)->bool{
  uint16_t next=adj[p]&~seen;
  while(next){int l=std::countr_zero(next);next&=next-1;seen|=1<<l;
   if(match[l]<0||self(self,match[l],seen)){match[l]=p;return true;}
  }return false;
 };
 for(int p=0;p<N;++p){uint16_t seen=0;if(augment(augment,p,seen))++total;}
 if(matching_cache.size()>2000000)matching_cache.clear();
 matching_cache.emplace(removed,total);return total;
}
Net seednet(int stars){
 Net gs{};int size=0;std::vector<int>roots;std::array<int,N>order{};
 for(int i=0;i<N;++i)order[i]=i;for(int i=N-1;i>0;--i)std::swap(order[i],order[ri(i+1)]);
 bool dual=ri(2);
 for(int t=0;t<stars;++t){int l=order[t];std::array<int,4>leaf{};int j=0;
  for(int d:{0,1,3,9})leaf[j++]=dual?N+(l-d+N)%N:(l+d)%N;
  for(int i=3;i>0;--i)std::swap(leaf[i],leaf[ri(i+1)]);
  int v=leaf[0];for(int i=1;i<4;++i){gs[size++]={v,leaf[i],false};v=INPUTS+size-1;}
  gs[size++]={v,dual?l:N+l,true};roots.push_back(INPUTS+size-1);
 }
 while(roots.size()>1){int j=ri(roots.size()),a=roots[j];roots.erase(roots.begin()+j);j=ri(roots.size());int b=roots[j];roots.erase(roots.begin()+j);roots.push_back(INPUTS+size);gs[size++]={a,b,false};}
 if(size!=count){std::cerr<<"bad seed size\n";std::exit(5);}return gs;
}
int errors(const Values&w){auto&o=w[INPUTS+count-1];int n=std::popcount(o[0]&~POS);for(int j=1;j<WORDS;++j)n+=std::popcount(o[j]);return n;}
int score(const Net&gs,Values&w,int weight,int from=0){
 for(int i=from;i<count;++i){auto&g=gs[i];auto&a=w[g.a];auto&b=w[g.b];auto&o=w[INPUTS+i];if(g.is_and){for(int j=0;j<WORDS;++j)o[j]=a[j]&b[j];}else{for(int j=0;j<WORDS;++j)o[j]=a[j]|b[j];}}
 auto pos=w[INPUTS+count-1][0]&POS;return weight*errors(w)+count-std::popcount(pos)+matching(pos);
}
void save(const Net&gs,const char*path,int value,const Values&w){std::ofstream f(path);f<<"gates "<<count<<" score "<<value<<" covered_edges "<<(w[INPUTS+count-1][0]&POS)<<"\n";for(int i=0;i<count;++i)f<<(gs[i].is_and?"and":"or")<<" "<<gs[i].a<<" "<<gs[i].b<<"\n";}
int main(int argc,char**argv){
 if(argc!=6)return 2;int seconds=std::stoi(argv[1]),weight=std::stoi(argv[5]);rngstate=std::stoull(argv[2]);
 std::ifstream f(argv[3]);std::vector<uint32_t>tests;uint32_t m;while(f>>m)tests.push_back(m);if(tests.size()!=TESTS)return 3;
 for(int i=0;i<INPUTS;++i)for(int j=0;j<TESTS;++j)if(tests[j]>>i&1)base[i][j/64]|=uint64_t(1)<<(j%64);
 for(int j=0;j<52;++j){int p=std::countr_zero(tests[j]&((1<<N)-1));int l=std::countr_zero(tests[j]>>N);edges[j]={p,l};}
 if(matching(0)!=13||matching(POS)!=0)return 4;
 for(int s=1;s<=13;++s){count=5*s-1;for(int rep=0;rep<25;++rep){auto gs=seednet(s);auto w=base;int z=score(gs,w,weight);if(z!=12||errors(w)){std::cerr<<"star baseline fail s="<<s<<" score="<<z<<"\n";return 4;}}}
 std::cout<<"star_baselines=PASS matching_empty=13 matching_full=0 weight="<<weight<<" seed="<<argv[2]<<std::endl;
 std::array<int,13>best;best.fill(10000);std::array<std::array<Net,16>,13>pool{};std::array<int,13>npool{};
 auto start=std::chrono::steady_clock::now();uint64_t iter=0,restarts=0;
 while(true){int s=2+ri(11);count=5*s-1;++restarts;Net gs=npool[s-1]&&ri(2)?pool[s-1][ri(npool[s-1])]:seednet(s);auto w=base;int value=score(gs,w,weight);double temp=ri(4)?0.03:0.25;
  for(int local=0;local<100000;++local){++iter;int k=ri(count);auto old=gs[k];int kind=ri(20);
   if(kind<8)gs[k].a=ri(INPUTS+k);else if(kind<16)gs[k].b=ri(INPUTS+k);else if(kind<19)gs[k].is_and=!gs[k].is_and;else gs[k]={ri(INPUTS+k),ri(INPUTS+k),bool(ri(2))};
   auto nw=w;int z=score(gs,nw,weight,k);
   if(z<=value||double(rnd()>>11)*0x1.0p-53<std::exp(double(value-z)/temp)){w=nw;value=z;}else gs[k]=old;
   int negatives=errors(w);
   if(!negatives&&value<best[s-1]){best[s-1]=value;std::cout<<"gates="<<count<<" best="<<value<<" edges="<<std::popcount(w[INPUTS+count-1][0]&POS)<<" matching_remaining="<<matching(w[INPUTS+count-1][0]&POS)<<" iterations="<<iter<<std::endl;}
   if(!negatives&&value<=12&&local%1000==0){if(npool[s-1]<16)pool[s-1][npool[s-1]++]=gs;else pool[s-1][ri(16)]=gs;}
   if(!negatives&&value<=11){save(gs,argv[4],value,w);std::cout<<"CANDIDATE block+starcover at most63 gates; needs independent validation"<<std::endl;return 0;}
   if((iter&65535)==0){auto elapsed=std::chrono::duration_cast<std::chrono::seconds>(std::chrono::steady_clock::now()-start).count();
    if(iter%4194304==0){std::cout<<"elapsed="<<elapsed<<" iterations="<<iter<<" matching_calls="<<matching_calls<<" matching_misses="<<matching_misses<<" restarts="<<restarts<<" best=";for(int j=1;j<12;++j)std::cout<<best[j]<<",";std::cout<<std::endl;}
    if(elapsed>=seconds){std::cout<<"STOP time_budget elapsed="<<elapsed<<" iterations="<<iter<<" matching_calls="<<matching_calls<<" matching_misses="<<matching_misses<<" restarts="<<restarts<<std::endl;return 1;}
   }
  }
 }
}
