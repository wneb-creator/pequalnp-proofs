#include <array>
#include <vector>
#include <algorithm>
#include <random>
#include <chrono>
#include <cmath>
#include <iostream>
#include <fstream>
using namespace std;
struct G {int op,a,b;};
struct C {array<G,10>g;int out=15;};
array<uint64_t,16> base;
uint64_t target,neg,low;
mt19937_64 rng(92);uint64_t evals;
int rr(int n){return rng()%n;}
struct R {int score,raw,nots;};
R assess(const C&c) {
  auto v=base;int nots=0;
  for(int i=0;i<10;i++) {auto g=c.g[i];nots+=g.op==2;v[6+i]=g.op==0?(v[g.a]&v[g.b]):g.op==1?(v[g.a]|v[g.b]):~v[g.a];}
  uint64_t d=v[c.out]^target;int raw=__builtin_popcountll(d);evals++;
  return {raw+3*__builtin_popcountll(d&low)+2*__builtin_popcountll(d&neg)+(nots==0?3:0),raw,nots};
}
void dump(const C&c,const R&r,const char*path) {
  ofstream f(path);f<<"score "<<r.score<<" raw "<<r.raw<<" nots "<<r.nots<<"\noutput "<<c.out<<"\n";
  for(auto g:c.g)f<<g.op<<' '<<g.a<<' '<<g.b<<'\n';
}
C seed(int del,int repl) {
  vector<G>gs={{1,0,3},{1,2,5},{1,1,4},{1,1,5},{1,1,3},{1,3,5},{0,0,9},{0,2,10},{0,4,11},{1,12,13},{1,15,14}};
  C c;int n=0;auto mp=[&](int x){return x==6+del?repl:x>6+del?x-1:x;};
  for(int i=0;i<11;i++)if(i!=del){auto g=gs[i];c.g[n++]={g.op,mp(g.a),mp(g.b)};}
  c.out=mp(16);return c;
}
void mutate(C&c) {
  int i=3+rr(7),t=rr(100);auto&g=c.g[i];
  if(t<40)g.a=rr(6+i);
  else if(t<80)g.b=rr(6+i);
  else if(t<98)g.op=rr(3);
  else c.out=6+rr(10);
}
int main(int argc,char**argv) {
  int secs=argc>1?atoi(argv[1]):300;if(argc>2)rng.seed(strtoull(argv[2],nullptr,10));
  for(int x=0;x<64;x++){
    uint64_t bit=uint64_t(1)<<x;
    for(int i=0;i<6;i++)if(x>>i&1)base[i]|=bit;
    bool f=0;for(int i=0;i<6;i++)f|=(x>>i&1)&&(x>>((i+1)%6)&1);
    if(f)target|=bit;else neg|=bit;if(__builtin_popcount((unsigned)x)<=2)low|=bit;
  }
  vector<pair<int,C>>ss;
  for(int d=3;d<11;d++)for(int r=0;r<6+d;r++){auto c=seed(d,r);ss.push_back({assess(c).score,c});}
  sort(ss.begin(),ss.end(),[](auto&a,auto&b){return a.first<b.first;});
  C champ=ss[0].second;R best=assess(champ);bool mono=false;
  cerr<<"initial best "<<best.score<<" raw "<<best.raw<<" seeds "<<ss.size()<<endl;
  auto start=chrono::steady_clock::now(),last=start;int restarts=0;
  while(chrono::duration<double>(chrono::steady_clock::now()-start).count()<secs){
    C c=restarts%3==0?champ:ss[rr(min(40,(int)ss.size()))].second;
    for(int i=0,n=rr(10);i<n;i++)mutate(c);
    R r=assess(c);double temp0=restarts%3==0?2.0:restarts%3==1?0.4:0.05;
    for(int it=0;it<10000;it++){
      C n=c;int changes=rr(100)<96?1:2+rr(2);for(int j=0;j<changes;j++)mutate(n);
      R nr=assess(n);double temp=temp0*(1.0-double(it)/10000)+0.02;
      if(nr.score<=r.score || double(rng())/UINT64_MAX<exp((r.score-nr.score)/temp)){c=n;r=nr;}
      if(r.raw==0){
        dump(c,r,"/tmp/oec/pequalnp-pilot-92/local-c6-exact.txt");
        if(r.nots>0){cerr<<"FOUND_WITH_NOT evals "<<evals<<endl;return 0;}
        if(!mono){cerr<<"FOUND_MONOTONE evals "<<evals<<endl;mono=true;}
      }
      if(r.score<best.score){best=r;champ=c;cerr<<"best "<<r.score<<" raw "<<r.raw<<" nots "<<r.nots<<" evals "<<evals<<endl;dump(c,r,"/tmp/oec/pequalnp-pilot-92/local-c6-best.txt");}
    }
    restarts++;auto now=chrono::steady_clock::now();
    if(chrono::duration<double>(now-last).count()>30){cerr<<"progress seconds "<<chrono::duration<double>(now-start).count()<<" best "<<best.score<<" evals "<<evals<<endl;last=now;}
  }
  dump(champ,best,"/tmp/oec/pequalnp-pilot-92/local-c6-best.txt");
  cerr<<"done best "<<best.score<<" raw "<<best.raw<<" nots "<<best.nots<<" evals "<<evals<<endl;return 1;
}
