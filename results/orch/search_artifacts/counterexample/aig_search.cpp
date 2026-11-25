#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <random>
#include <vector>
using U=uint64_t;using TT=std::array<U,16>;
struct Gate{int a,b;};
struct Circ{std::array<Gate,17> gs;std::array<TT,27> w;int phase,score;};
std::mt19937_64 rng(1702592);int rnd(int n){return rng()%n;}
const std::array<std::pair<int,int>,15> edges={{{0,1},{1,2},{2,3},{3,4},{4,0},{0,5},{1,6},{2,7},{3,8},{4,9},{5,7},{7,9},{9,6},{6,8},{8,5}}};
std::array<TT,10> inp;TT target;std::vector<int> covers;
int eval(Circ&c,int start=0){
 for(int j=start;j<17;j++){
  auto g=c.gs[j];U an=U(0)-U(g.a&1),bn=U(0)-U(g.b&1);
  for(int k=0;k<16;k++)c.w[10+j][k]=(c.w[g.a/2][k]^an)&(c.w[g.b/2][k]^bn);
 }
 int score=0;U ph=U(0)-U(c.phase);for(int k=0;k<16;k++)score+=std::popcount((c.w[26][k]^ph)^target[k]);
 return c.score=score;
}
Circ base(){Circ c;for(int i=0;i<10;i++)c.w[i]=inp[i];c.phase=1;return c;}
Circ seeded(){
 int cover=covers[rnd(covers.size())];std::vector<int> ns[10];
 for(auto [a,b]:edges){if(!(cover>>a&1))std::swap(a,b);else if((cover>>b&1)&&rnd(2))std::swap(a,b);ns[a].push_back(b);}
 struct Old{int op,a,b;};std::vector<Old> old;std::vector<int>sums,order;
 for(int i=0;i<10;i++)if(!ns[i].empty())order.push_back(i);std::shuffle(order.begin(),order.end(),rng);
 for(int i:order){
  std::shuffle(ns[i].begin(),ns[i].end(),rng);int x=ns[i][0];
  for(int k=1;k<(int)ns[i].size();k++){old.push_back({1,x,ns[i][k]});x=9+old.size();}
  old.push_back({0,i,x});sums.push_back(9+old.size());
 }
 while(sums.size()>1){int k=rnd(sums.size()),a=sums[k];sums.erase(sums.begin()+k);k=rnd(sums.size());int b=sums[k];sums.erase(sums.begin()+k);old.push_back({1,a,b});sums.push_back(9+old.size());}
 std::vector<Gate> gs;int ref[30];for(int i=0;i<10;i++)ref[i]=2*i;
 for(int j=0;j<20;j++){auto g=old[j];gs.push_back({ref[g.a]^g.op,ref[g.b]^g.op});ref[j+10]=2*(j+10)+g.op;}
 for(int z=0;z<3;z++){
  int rem=rnd(gs.size()-1),sub=rnd(2)?gs[rem].a:gs[rem].b;
  auto tr=[&](int x){if(x/2==10+rem)x=sub^(x&1);return x/2>10+rem?x-2:x;};
  gs.erase(gs.begin()+rem);for(auto &g:gs){g.a=tr(g.a);g.b=tr(g.b);}
 }
 Circ c=base();for(int j=0;j<17;j++)c.gs[j]=gs[j];eval(c);return c;
}
void print(const Circ&c,unsigned long long it,double seconds){
 std::printf("BEST errors=%d phase=%d iterations=%llu seconds=%.1f\n",c.score,c.phase,it,seconds);
 for(int j=0;j<17;j++)std::printf("%d %d %d\n",j+10,c.gs[j].a,c.gs[j].b);std::fflush(stdout);
}
int main(int argc,char**argv){
 int duration=argc>1?std::atoi(argv[1]):600;
 for(int r=0;r<1024;r++){for(int i=0;i<10;i++)if(r>>i&1)inp[i][r/64]|=U(1)<<(r%64);for(auto[a,b]:edges)if((r>>a&1)&&(r>>b&1)){target[r/64]|=U(1)<<(r%64);break;}}
 for(int c=0;c<1024;c++)if(std::popcount((unsigned)c)==6){bool ok=true;for(auto[a,b]:edges)if(!((c>>a&1)||(c>>b&1)))ok=false;if(ok)covers.push_back(c);}
 auto t=std::chrono::steady_clock::now();std::vector<Circ> pop;for(int i=0;i<128;i++)pop.push_back(seeded());Circ best=pop[0];double seconds=0;unsigned long long it=0;
 for(;;it++){
  if(it%65536==0){seconds=std::chrono::duration<double>(std::chrono::steady_clock::now()-t).count();if(seconds>=duration)break;}
  int slot=rnd(128);Circ old=pop[slot],c=old;int lo=17;
  int changes=1+(rnd(100)<15)+(rnd(100)<5?rnd(7):0);
  for(int z=0;z<changes;z++){int j=rnd(17);lo=std::min(lo,j);if(rnd(2))c.gs[j].a=rnd(2*(10+j));else c.gs[j].b=rnd(2*(10+j));}
  if(rnd(10000)==0)c.phase^=1;eval(c,lo);
  double temp=slot%8==0?2.0:slot%8==1?0.8:slot%8==2?0.2:0;
  if(c.score<=old.score||(temp>0&&double(rng())/double(UINT64_MAX)<std::exp((old.score-c.score)/temp)))pop[slot]=c;
  if(c.score<best.score){best=c;print(c,it,seconds);if(!c.score)return 0;}
  if(it%32768==0)pop[rnd(128)]=seeded();if(it%65536==0)pop[rnd(128)]=best;
 }
 print(best,it,seconds);
}
