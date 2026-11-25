#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <vector>
struct Gate { int a,b; bool is_and; };
using Net=std::array<Gate,26>;
uint64_t rng_state=1387639;
uint64_t rnd(){rng_state^=rng_state<<13;rng_state^=rng_state>>7;return rng_state^=rng_state<<17;}
int ri(int n){return rnd()%n;}
const uint64_t posmask=(uint64_t(1)<<21)-1;
const uint64_t negmask=((uint64_t(1)<<58)-1)^posmask;
std::array<uint64_t,40> base;
std::vector<uint8_t> tau(1<<21,14);
std::vector<std::pair<int,int>> edges;
int count;
Net seednet(){
 std::vector<Gate> gs;std::vector<int> outs;
 std::array<int,7> order{0,1,2,3,4,5,6};
 for(int i=6;i>0;--i)std::swap(order[i],order[ri(i+1)]);
 for(int t=0;t<(count+2)/4;++t){
  int l=order[t];std::array<int,3> p{l,(l+1)%7,(l+3)%7};
  for(int i=2;i>0;--i)std::swap(p[i],p[ri(i+1)]);
  int n=14+gs.size();gs.push_back({p[0],p[1],false});gs.push_back({n,p[2],false});gs.push_back({n+1,7+l,true});outs.push_back(n+2);
 }
 while(outs.size()>1){
  int i=ri(outs.size()),a=outs[i];outs.erase(outs.begin()+i);
  i=ri(outs.size());int b=outs[i];outs.erase(outs.begin()+i);
  outs.push_back(14+gs.size());gs.push_back({a,b,false});
 }
 int rem=ri(count),repl=ri(2)?gs[rem].a:gs[rem].b;
 Net out{};int j=0;auto rw=[&](int w){if(w==14+rem)w=repl;return w>14+rem?w-1:w;};
 for(int i=0;i<count+1;++i)if(i!=rem)out[j++]={rw(gs[i].a),rw(gs[i].b),gs[i].is_and};
 return out;
}
int eval(const Net&gs,std::array<uint64_t,40>&w,int from=0){
 for(int j=from;j<count;++j)w[14+j]=gs[j].is_and?(w[gs[j].a]&w[gs[j].b]):(w[gs[j].a]|w[gs[j].b]);
 auto out=w[13+count];auto pos=out&posmask;
 return 2*std::popcount(out&negmask)+count-std::popcount(pos)+tau[pos];
}
void save(const Net&gs,const char*path,int score,uint64_t val){
 std::ofstream f(path);f<<"gates "<<count<<" score "<<score<<" positive_mask "<<(val&posmask)<<" negative_mask "<<(val&negmask)<<"\n";
 for(int j=0;j<count;++j){auto g=gs[j];f<<(g.is_and?"and":"or")<<" "<<g.a<<" "<<g.b<<"\n";}
}
int main(int argc,char**argv){
 if(argc!=4)return 2;int secs=std::stoi(argv[1]);std::ifstream f(argv[2]);std::vector<int>tests;int m;while(f>>m)tests.push_back(m);if(tests.size()!=58)return 3;
 for(int i=0;i<14;++i)for(int j=0;j<58;++j)if(tests[j]>>i&1)base[i]|=uint64_t(1)<<j;
 for(int l=0;l<7;++l)for(int p=0;p<7;++p)if(p==l||p==(l+1)%7||p==(l+3)%7)edges.emplace_back(p,7+l);
 for(int v=0;v<(1<<14);++v){int unc=0;for(int j=0;j<21;++j){auto[a,b]=edges[j];if(!((v>>a&1)||(v>>b&1)))unc|=1<<j;}tau[unc]=std::min<int>(tau[unc],std::popcount((unsigned)v));}
 for(int i=0;i<21;++i)for(int s=0;s<(1<<21);++s)if(s>>i&1)tau[s]=std::min(tau[s],tau[s^(1<<i)]);
 std::cout<<"tau(empty)="<<int(tau[0])<<" tau(all)="<<int(tau[(1<<21)-1])<<std::endl;
 auto start=std::chrono::steady_clock::now();uint64_t it=0,restarts=0;std::array<int,7>best;best.fill(1000);
 std::array<std::array<Net,16>,7>pool{};std::array<int,7>npool{};
 while(true){
  int s=ri(6)+2;count=4*s-2;++restarts;Net gs=npool[s-1]&&ri(2)?pool[s-1][ri(npool[s-1])]:seednet();auto w=base;int score=eval(gs,w);double temp=ri(4)?0.02:0.2;
  for(int local=0;local<50000;++local){
   ++it;int k=ri(count);auto old=gs[k];int kind=ri(20);
   if(kind<8)gs[k].a=ri(14+k);else if(kind<16)gs[k].b=ri(14+k);else if(kind<19)gs[k].is_and=!gs[k].is_and;else gs[k]={ri(14+k),ri(14+k),bool(ri(2))};
   auto nw=w;int z=eval(gs,nw,k);
   if(z<=score||double(rnd()>>11)*0x1.0p-53<std::exp(double(score-z)/temp)){w=nw;score=z;}else gs[k]=old;
   if(score<best[s-1] && !(w[13+count]&negmask)){best[s-1]=score;std::cout<<"gates="<<count<<" best_score="<<score<<" edges="<<std::popcount(w[13+count]&posmask)<<" tau_remaining="<<int(tau[w[13+count]&posmask])<<" negatives="<<std::popcount(w[13+count]&negmask)<<" iterations="<<it<<std::endl;}
   if(score<=7&&local%1000==0){pool[s-1][ri(16)]=gs;if(npool[s-1]<16)pool[s-1][npool[s-1]++]=gs;}
   if(score<=5 && !(w[13+count]&negmask)){save(gs,argv[3],score,w[13+count]);std::cout<<"CANDIDATE needing independent full truth validation"<<std::endl;return 0;}
   if(it%10000000==0){int elapsed=std::chrono::duration_cast<std::chrono::seconds>(std::chrono::steady_clock::now()-start).count();std::cout<<"elapsed="<<elapsed<<" iterations="<<it<<" restarts="<<restarts<<" scores=";for(int j=1;j<7;++j)std::cout<<best[j]<<",";std::cout<<std::endl;if(elapsed>=secs)return 1;}
  }
 }
}
