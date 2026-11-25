#include <array>
#include <vector>
#include <chrono>
#include <random>
#include <iostream>
#include <fstream>
#include <cmath>
using namespace std;
constexpr int N=32;
using TT=array<uint64_t,16>;
struct G {int op,a,b;};
struct C {array<G,N> g;int out=10+N-1;};
array<TT,10+N> base;
TT goal,low,neg;
mt19937_64 rng(92);
uint64_t evals=0;
int rr(int n){return rng()%n;}
struct Result {int score,raw,used,nots;};
Result assess(const C&c) {
  auto v=base;uint64_t active=uint64_t(1)<<c.out;
  for(int i=0;i<N;i++)for(int k=0;k<16;k++) {
    auto g=c.g[i];
    v[10+i][k]=g.op==0?(v[g.a][k]&v[g.b][k]):g.op==1?(v[g.a][k]|v[g.b][k]):~v[g.a][k];
  }
  int used=0,nots=0;
  for(int i=N-1;i>=0;i--)if(active>>(i+10)&1) {
    used++;auto g=c.g[i];nots+=g.op==2;
    active|=uint64_t(1)<<g.a;
    if(g.op!=2)active|=uint64_t(1)<<g.b;
  }
  int err=0,raw=0;
  for(int k=0;k<16;k++) {
    uint64_t d=v[c.out][k]^goal[k];int pc=__builtin_popcountll(d);
    raw+=pc;err+=pc+8*__builtin_popcountll(d&low[k])+4*__builtin_popcountll(d&neg[k]);
  }
  int compiled=used+(nots==0);
  evals++;
  return {err*100+compiled*5,raw,used,nots};
}
void dump(const C&c,const Result&r,const char*path) {
  ofstream f(path);f<<"score "<<r.score<<" raw "<<r.raw<<" used "<<r.used<<" nots "<<r.nots<<"\noutput "<<c.out<<"\n";
  for(auto g:c.g)f<<g.op<<' '<<g.a<<' '<<g.b<<'\n';
}
C seed() {
  vector<G> orig={{1,9,5},{1,0,9},{1,0,6},{1,7,3},{0,1,12},{1,6,5},{1,11,3},{1,13,1},{1,14,2},{0,12,15},{0,4,16},{0,19,11},{1,7,21},{0,18,17},{1,20,23},{1,3,15},{0,25,8},{0,22,10},{1,27,26},{1,24,28}};
  C c;array<int,30> mp;for(int i=0;i<10;i++)mp[i]=i;
  for(int i=0;i<N;i++)c.g[i]={rr(3),rr(10+i),rr(10+i)};
  for(int i=0;i<20;i++){int p=i*(N-1)/19;mp[10+i]=10+p;auto g=orig[i];c.g[p]={g.op,mp[g.a],mp[g.b]};}
  c.out=mp[29];return c;
}
void mutate(C&c) {
  int i=rr(N),t=rr(100);auto&g=c.g[i];
  if(t<44)g.a=rr(10+i);
  else if(t<88)g.b=rr(10+i);
  else if(t<99)g.op=rr(3);
  else c.out=10+rr(N);
}
int main(int argc,char**argv) {
  int seconds=argc>1?atoi(argv[1]):900;
  if(argc>2)rng.seed(strtoull(argv[2],nullptr,10));
  const int es[15][2]={{0,1},{1,2},{2,3},{3,4},{4,0},{0,5},{1,6},{2,7},{3,8},{4,9},{5,7},{7,9},{9,6},{6,8},{8,5}};
  for(int x=0;x<1024;x++) {
    uint64_t b=uint64_t(1)<<(x%64);int k=x/64;
    for(int i=0;i<10;i++)if(x>>i&1)base[i][k]|=b;
    bool f=0;for(auto e:es)f|=(x>>e[0]&1)&&(x>>e[1]&1);
    if(f)goal[k]|=b;else neg[k]|=b;
    if(__builtin_popcount((unsigned)x)<=3)low[k]|=b;
  }
  C champion=seed();Result best=assess(champion);
  cerr<<"initial score "<<best.score<<" used "<<best.used<<" nots "<<best.nots<<" raw "<<best.raw<<endl;
  auto start=chrono::steady_clock::now(),last=start;
  int restarts=0;
  while(chrono::duration<double>(chrono::steady_clock::now()-start).count()<seconds) {
    C c=(restarts%5==0)?seed():champion;Result r=assess(c);
    for(int it=0;it<200000;it++) {
      C n=c;int m=rr(100)<95?1:2+rr(3);for(int j=0;j<m;j++)mutate(n);
      Result nr=assess(n);double temp=(it<1000 && restarts%10==0)?50.0:1.1;
      if(nr.score<=r.score || double(rng())/UINT64_MAX<exp((r.score-nr.score)/temp)){c=n;r=nr;}
      if(r.raw==0 && r.score<=best.score) {
        if(r.score<best.score) {
          best=r;champion=c;
          cerr<<"best score "<<best.score<<" used "<<best.used<<" nots "<<best.nots<<" evals "<<evals<<endl;
          dump(c,r,"/tmp/oec/pequalnp-pilot-92/local-cgp-best.txt");
          if(r.used+(r.nots==0)<=19){cerr<<"FOUND"<<endl;return 0;}
        }else if(rr(4000)==0)champion=c;
      }
      if((it&8191)==0 && chrono::duration<double>(chrono::steady_clock::now()-start).count()>seconds)break;
    }
    restarts++;
    auto now=chrono::steady_clock::now();
    if(chrono::duration<double>(now-last).count()>30) {
      cerr<<"progress seconds "<<chrono::duration<double>(now-start).count()<<" score "<<best.score<<" evals "<<evals<<" restarts "<<restarts<<endl;last=now;
    }
  }
  dump(champion,assess(champion),"/tmp/oec/pequalnp-pilot-92/local-cgp-best.txt");
  cerr<<"done best "<<best.score<<" evals "<<evals<<endl;
  return 1;
}
