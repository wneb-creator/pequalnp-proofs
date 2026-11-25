#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <random>
#include <vector>
using U=uint64_t;
using TT=std::array<U,16>;
struct Gate {int op,a,b;};
struct Circ {std::array<Gate,19> gs;std::array<TT,29> w;int score;};
std::mt19937_64 rng(2592);
int rnd(int n){return rng()%n;}
const std::array<std::pair<int,int>,15> edges={{{0,1},{1,2},{2,3},{3,4},{4,0},{0,5},{1,6},{2,7},{3,8},{4,9},{5,7},{7,9},{9,6},{6,8},{8,5}}};
TT target;
std::array<TT,10> inp;
bool activeMode=false;
int eval(Circ &c,int start=0){
 int nots=0;
 for(int i=0;i<19;i++){
  auto g=c.gs[i];nots+=g.op==2;
  if(i<start)continue;
  for(int k=0;k<16;k++)c.w[10+i][k]=g.op==0?(c.w[g.a][k]&c.w[g.b][k]):g.op==1?(c.w[g.a][k]|c.w[g.b][k]):~c.w[g.a][k];
 }
 int score=0;
 for(int k=0;k<16;k++) score+=std::popcount(c.w[28][k]^target[k]);
 int activeNots=0;
 if(activeMode){
  bool live[29]={};live[28]=true;
  for(int i=18;i>=0;i--)if(live[i+10]){
   auto g=c.gs[i];live[g.a]=true;if(g.op!=2)live[g.b]=true;else activeNots++;
  }
 }
 c.score=score+((activeMode?activeNots:nots)==0?16:0);
 return c.score;
}
Circ base(){Circ c;for(int i=0;i<10;i++)c.w[i]=inp[i];return c;}
std::vector<int> covers;
Circ seeded(){
 int cover=covers[rnd(covers.size())];std::vector<int> ns[10];
 for(auto [a,b]:edges){
  if(!(cover>>a&1))std::swap(a,b);
  else if((cover>>b&1)&&rnd(2))std::swap(a,b);
  ns[a].push_back(b);
 }
 std::vector<Gate> gs;std::vector<int> sums;
 std::vector<int> order;for(int i=0;i<10;i++)if(!ns[i].empty())order.push_back(i);
 std::shuffle(order.begin(),order.end(),rng);
 for(int i:order){
  std::shuffle(ns[i].begin(),ns[i].end(),rng);int p=ns[i][0];
  for(int k=1;k<(int)ns[i].size();k++){gs.push_back({1,p,ns[i][k]});p=9+gs.size();}
  gs.push_back({0,i,p});sums.push_back(9+gs.size());
 }
 while(sums.size()>1){
  int a=rnd(sums.size());int x=sums[a];sums.erase(sums.begin()+a);
  int b=rnd(sums.size());int y=sums[b];sums.erase(sums.begin()+b);
  gs.push_back({1,x,y});sums.push_back(9+gs.size());
 }
 // Remove one gate and bypass it with either one of its operands.
 int rem=rnd(19),sub=rnd(2)?gs[rem].a:gs[rem].b;
 auto tr=[&](int x){if(x==10+rem)x=sub;return x>10+rem?x-1:x;};
 Circ c=base();int k=0;
 for(int i=0;i<20;i++)if(i!=rem){auto g=gs[i];c.gs[k++]={g.op,tr(g.a),tr(g.b)};}
 int no=rnd(19);c.gs[no].op=2;
 eval(c);return c;
}
Circ randomc(){Circ c=base();for(int i=0;i<19;i++)c.gs[i]={rnd(10)==0?2:rnd(2),rnd(10+i),rnd(10+i)};eval(c);return c;}
void print(const Circ&c,unsigned long long iter,double secs){
 int nots=0;for(auto g:c.gs)nots+=g.op==2;
 std::printf("BEST score=%d nots=%d iter=%llu seconds=%.1f\n",c.score,nots,iter,secs);
 for(int i=0;i<19;i++){auto g=c.gs[i];std::printf("%d %c %d %d\n",10+i,"&|!"[g.op],g.a,g.b);}
 std::fflush(stdout);
}
int main(int argc,char**argv){
 int duration=argc>1?std::atoi(argv[1]):600;
 activeMode=argc>2;
 for(int x=0;x<1024;x++){
  for(int i=0;i<10;i++)if(x>>i&1)inp[i][x/64]|=U(1)<<(x%64);
  for(auto [a,b]:edges)if((x>>a&1)&&(x>>b&1)){target[x/64]|=U(1)<<(x%64);break;}
 }
 for(int c=0;c<1024;c++)if(std::popcount((unsigned)c)==6){bool ok=true;for(auto [a,b]:edges)if(!((c>>a&1)||(c>>b&1)))ok=false;if(ok)covers.push_back(c);}
 std::printf("covers=%zu\n",covers.size());
 auto t=std::chrono::steady_clock::now();
 std::vector<Circ> pop;for(int i=0;i<128;i++)pop.push_back(seeded());
 Circ best=pop[0];unsigned long long it=0;double seconds=0;
 for(;;it++){
  if(it%65536==0){seconds=std::chrono::duration<double>(std::chrono::steady_clock::now()-t).count();if(seconds>duration)break;}
  int slot=rnd(pop.size());Circ old=pop[slot];Circ c=old;int lo=19;
  int changes=1+(rnd(100)<12)+(rnd(100)<5)+(rnd(100)<2?rnd(7):0);
  for(int j=0;j<changes;j++){
   int i=rnd(19);lo=std::min(lo,i);int mode=rnd(7);
   if(mode<2)c.gs[i].op=rnd(7)==0?2:rnd(2);
   else if(mode<4)c.gs[i].a=rnd(10+i);
   else if(mode<6)c.gs[i].b=rnd(10+i);
   else c.gs[i]={rnd(7)==0?2:rnd(2),rnd(10+i),rnd(10+i)};
  }
  eval(c,lo);
  double temp=slot%8==0?1.0:slot%8==1?0.35:0.0;
  if(c.score<=old.score||(temp>0&&double(rng())/double(UINT64_MAX)<std::exp((old.score-c.score)/temp)))pop[slot]=c;
  if(c.score<best.score){best=c;print(c,it,seconds);if(c.score==0)return 0;}
  if(it%32768==0){int j=rnd(pop.size());pop[j]=rnd(4)?seeded():randomc();}
  if(it%65536==0){int j=rnd(pop.size());pop[j]=best;}
 }
 print(best,it,seconds);
}
