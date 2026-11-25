#include <array>
#include <algorithm>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <random>
#include <vector>
using namespace std;
using TT=array<uint64_t,16>;
struct Gate { int op,a,b; };
struct Circ { array<Gate,19> g; int out=28; };
array<TT,32> base;
TT goal,low,negative;
mt19937_64 rng;
uint64_t evaluations=0;
int rr(int n) { return rng()%n; }
int score(const Circ& c,int* raw=nullptr) {
  auto v=base;
  int nn=0;
  for(int i=0;i<19;i++) {
    auto g=c.g[i]; nn+=(g.op==2);
    for(int k=0;k<16;k++) {
      if(g.op==0) v[10+i][k]=v[g.a][k]&v[g.b][k];
      if(g.op==1) v[10+i][k]=v[g.a][k]|v[g.b][k];
      if(g.op==2) v[10+i][k]=~v[g.a][k];
      if(g.op==3) v[10+i][k]=0;
      if(g.op==4) v[10+i][k]=~uint64_t(0);
    }
  }
  int s=0,r=0;
  for(int k=0;k<16;k++) {
    uint64_t d=v[c.out][k]^goal[k];
    int pc=__builtin_popcountll(d);
    r+=pc; s+=pc+8*__builtin_popcountll(d&low[k])+4*__builtin_popcountll(d&negative[k]);
  }
  s+=nn==0?25:nn>4?25*(nn-4):0;
  if(raw) *raw=r;
  evaluations++;
  return s;
}
void dump(const Circ& c,int s,const char* path) {
  ofstream f(path);
  f<<"score "<<s<<"\noutput "<<c.out<<"\n";
  for(auto g:c.g) f<<g.op<<' '<<g.a<<' '<<g.b<<'\n';
  f.flush();
}
Circ seed(int del,int redirect) {
  vector<Gate> orig={{1,9,5},{1,0,9},{1,0,6},{1,7,3},{0,1,12},{1,6,5},{1,11,3},{1,13,1},{1,14,2},{0,12,15},{0,4,16},{0,19,11},{1,7,21},{0,18,17},{1,20,23},{1,3,15},{0,25,8},{0,22,10},{1,27,26},{1,24,28}};
  Circ c; int j=0;
  auto map=[&](int x) { return x==del+10?redirect:x>del+10?x-1:x; };
  for(int i=0;i<20;i++) if(i!=del) {
    auto g=orig[i]; g.a=map(g.a);g.b=map(g.b);c.g[j++]=g;
  }
  c.out=map(29); return c;
}
void mutate(Circ& c) {
  int i=rr(19),t=rr(100);
  auto& g=c.g[i];
  if(t<41) g.a=rr(10+i);
  else if(t<82) g.b=rr(10+i);
  else if(t<96) { int z=rr(100); g.op=z<42?0:z<84?1:z<98?2:z==98?3:4; }
  else if(t<99) {g.a=rr(10+i);g.b=rr(10+i);}
  else c.out=10+rr(19);
}
int main(int argc,char**argv) {
  int seconds=argc>1?atoi(argv[1]):600;
  rng.seed(argc>2?strtoull(argv[2],nullptr,10):17);
  const int edges[15][2]={{0,1},{1,2},{2,3},{3,4},{4,0},{0,5},{1,6},{2,7},{3,8},{4,9},{5,7},{7,9},{9,6},{6,8},{8,5}};
  for(int x=0;x<1024;x++) {
    uint64_t bit=uint64_t(1)<<(x%64);int k=x/64;
    for(int i=0;i<10;i++) if(x>>i&1)base[i][k]|=bit;
    bool f=false;for(auto e:edges)f|=(x>>e[0]&1)&&(x>>e[1]&1);
    if(f)goal[k]|=bit;else negative[k]|=bit;
    if(__builtin_popcount((unsigned)x)<=3)low[k]|=bit;
  }
  vector<pair<int,Circ>> seeds;
  int best=100000;Circ champion;
  for(int d=0;d<20;d++)for(int r=0;r<10+d;r++) {
    Circ c=seed(d,r);int s=score(c);seeds.push_back({s,c});
    if(s<best){best=s;champion=c;}
  }
  sort(seeds.begin(),seeds.end(),[](auto&a,auto&b){return a.first<b.first;});
  cerr<<"initial_best "<<best<<" seeds "<<seeds.size()<<endl;
  auto start=chrono::steady_clock::now();auto last=start;
  int restarts=0,iterations=0;
  for(;;) {
    auto now=chrono::steady_clock::now();
    if(chrono::duration<double>(now-start).count()>seconds)break;
    Circ c=(restarts%4==0)?champion:seeds[rr(min(100,(int)seeds.size()))].second;
    int perturb=2+rr(14);
    for(int k=0;k<perturb;k++)mutate(c);
    int s=score(c),localbest=s,stall=0;
    double temp0=(restarts%3==0)?5.0:restarts%3==1?1.0:0.15;
    int steps=25000;
    for(int t=0;t<steps;t++) {
      Circ next=c;int m=rr(100)<98?1:2+rr(3);for(int j=0;j<m;j++)mutate(next);
      int ns=score(next);
      double temperature=temp0*(1.0-double(t)/steps)+0.03;
      if(ns<=s || double(rng())/double(UINT64_MAX)<exp((s-ns)/temperature)) {c=next;s=ns;}
      if(s<localbest){localbest=s;stall=0;}else stall++;
      if(s<best) {
        best=s;champion=c;int raw;score(c,&raw);
        cerr<<"best "<<best<<" raw "<<raw<<" evals "<<evaluations<<" restart "<<restarts<<endl;
        dump(c,s,"/tmp/oec/pequalnp-pilot-92/local-best.txt");
        if(best==0) {cerr<<"FOUND"<<endl;return 0;}
      }
      if((t&2047)==0 && chrono::duration<double>(chrono::steady_clock::now()-start).count()>seconds)break;
    }
    restarts++;
    now=chrono::steady_clock::now();
    if(chrono::duration<double>(now-last).count()>30) {
      cerr<<"progress seconds "<<chrono::duration<double>(now-start).count()<<" best "<<best<<" evals "<<evaluations<<" restarts "<<restarts<<endl;
      last=now;
    }
  }
  cerr<<"done best "<<best<<" evaluations "<<evaluations<<" restarts "<<restarts<<endl;
  dump(champion,best,"/tmp/oec/pequalnp-pilot-92/local-best.txt");
  return best==0?0:1;
}
