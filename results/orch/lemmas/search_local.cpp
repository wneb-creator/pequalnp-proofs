#include <array>
#include <bit>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <random>
#include <vector>
#include "search_seeds.hpp"

using TT = std::array<uint64_t,16>;
struct Gate {int op,a,b;};
struct Circ { std::array<Gate,19> gates; std::array<TT,29> wires; int score,wrong; };
TT target, masks[5];
int weight[5]={32,12,3,1,1};
int noNotPenalty=8;
bool randomOrder=true;
std::mt19937_64 gen;
int rnd(int n) {return gen()%n;}
double unif() {return double(gen()>>11)*0x1.0p-53;}

void evaluate(Circ &c, int from=0) {
  for(int j=from;j<19;++j) {
    const auto &g=c.gates[j];
    for(int k=0;k<16;++k) c.wires[10+j][k]=g.op==0 ? c.wires[g.a][k]&c.wires[g.b][k] : g.op==1 ? c.wires[g.a][k]|c.wires[g.b][k] : ~c.wires[g.a][k];
  }
  c.score=0;c.wrong=0;
  for(int k=0;k<16;++k) {
    uint64_t e=c.wires[28][k]^target[k];
    c.wrong+=std::popcount(e);
    for(int t=0;t<5;++t) c.score+=weight[t]*std::popcount(e&masks[t][k]);
  }
  bool hasnot=false;
  for(auto g:c.gates) hasnot|=g.op==2;
  if(!hasnot)c.score+=noNotPenalty;
}

Circ start() {
  Circ c{};
  for(int i=0;i<10;++i) for(int r=0;r<1024;++r) if(r>>i&1)c.wires[i][r/64]|=uint64_t(1)<<(r%64);
  int s=rnd(40);
  Gate reordered[20];int where[20];for(auto &x:where)x=-1;
  for(int pos=0;pos<20;++pos) {
    if(!randomOrder) {reordered[pos]={SEEDS[s][pos][0],SEEDS[s][pos][1],SEEDS[s][pos][2]};continue;}
    std::vector<int> available;
    for(int j=0;j<20;++j)if(where[j]<0 && (SEEDS[s][j][1]<10 || where[SEEDS[s][j][1]-10]>=0) && (SEEDS[s][j][2]<10 || where[SEEDS[s][j][2]-10]>=0))available.push_back(j);
    int j=available[rnd(available.size())];
    auto relabel=[&](int v){return v<10?v:10+where[v-10];};
    reordered[pos]={SEEDS[s][j][0],relabel(SEEDS[s][j][1]),relabel(SEEDS[s][j][2])};where[j]=pos;
  }
  int rem=rnd(19),side=rnd(2);
  int sub=(randomOrder ? side!=0 : side==0)?reordered[rem].a:reordered[rem].b;
  for(int j=0,jj=0;j<20;++j) if(j!=rem) {
    auto fix=[&](int w) {if(w==10+rem)w=sub;return w>10+rem ? w-1:w;};
    c.gates[jj++]={reordered[j].op,fix(reordered[j].a),fix(reordered[j].b)};
  }
  evaluate(c);
  return c;
}

void mutate(Circ &c, int changes) {
  int from=19;
  for(int i=0;i<changes;++i) {
    int j=rnd(19);from=std::min(from,j);
    int p=rnd(10);
    if(p<4)c.gates[j].a=rnd(10+j);
    else if(p<8)c.gates[j].b=rnd(10+j);
    else c.gates[j].op=rnd(5)==0 ? 2:rnd(2);
  }
  evaluate(c,from);
}

void show(const Circ &c, uint64_t steps, double elapsed) {
  int nots=0;for(auto g:c.gates)nots+=g.op==2;
  std::printf("steps=%llu elapsed=%.2f wrong=%d score=%d nots=%d\n",(unsigned long long)steps,elapsed,c.wrong,c.score,nots);
  for(int j=0;j<19;++j)std::printf("%d %d %d %d\n",10+j,c.gates[j].op,c.gates[j].a,c.gates[j].b);
  std::fflush(stdout);
}

int main(int argc,char **argv) {
  uint64_t seed=argc>1 ? std::strtoull(argv[1],nullptr,10):1;gen.seed(seed);
  double seconds=argc>2 ? std::atof(argv[2]):600;
  noNotPenalty=argc>3 ? std::atoi(argv[3]):8;
  randomOrder=argc>4 ? std::atoi(argv[4])!=0:true;
  int edges[15][2]={{0,1},{1,2},{2,3},{3,4},{4,0},{0,5},{1,6},{2,7},{3,8},{4,9},{5,7},{7,9},{9,6},{6,8},{8,5}};
  for(int r=0;r<1024;++r) {
    bool y=false;for(auto e:edges)y|=(r>>e[0]&r>>e[1]&1);
    if(y)target[r/64]|=uint64_t(1)<<(r%64);
    int n=std::popcount(unsigned(r));int group=n<=2?0:n==3?1:n==4?2:n==5?3:4;
    masks[group][r/64]|=uint64_t(1)<<(r%64);
  }
  auto begin=std::chrono::steady_clock::now();
  auto elapsed=[&](){return std::chrono::duration<double>(std::chrono::steady_clock::now()-begin).count();};
  Circ best=start(),current=best;std::vector<Circ> bank;
  int bestwrong=best.wrong,bestscore=best.score,bestnot=1025;
  show(best,0,elapsed());
  for(uint64_t it=1;;++it) {
    if((it&65535)==0 && elapsed()>seconds)break;
    if(it%20000==0) {
      if(bank.size()&&rnd(3))current=bank[rnd(bank.size())];else current=start();
      mutate(current,1+rnd(4));
    }
    double t=1.0+40.0*std::pow(1.0-double(it%20000)/20000.0,4);
    Circ candidate=current;
    int changes=rnd(10)==0?2+rnd(3):1;
    mutate(candidate,changes);
    bool hasnot=false;for(auto g:candidate.gates)hasnot|=g.op==2;
    if(candidate.score<=current.score || unif()<std::exp(double(current.score-candidate.score)/t))current=candidate;
    if(candidate.score<bestscore || candidate.wrong<bestwrong || (hasnot && candidate.wrong<bestnot)) {
      bestscore=std::min(bestscore,candidate.score);bestwrong=std::min(bestwrong,candidate.wrong);best=candidate;
      if(hasnot)bestnot=std::min(bestnot,candidate.wrong);
      show(candidate,it,elapsed());
    }
    if(candidate.score<=bestscore+30 && it%100==0) {
      if(bank.size()<128)bank.push_back(candidate);else bank[rnd(bank.size())]=candidate;
    }
    if(candidate.wrong==0) {show(candidate,it,elapsed());return 0;}
  }
  show(best,0,elapsed());return 1;
}
