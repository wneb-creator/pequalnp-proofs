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
struct Circ { array<Gate,17> g; int out=26; };
array<TT,32> base;
TT goal,low,negative,care;
mt19937_64 rng;
uint64_t evaluations=0;
int rr(int n) { return rng()%n; }
int score(const Circ& c,int* raw=nullptr) {
  auto v=base;
  int nn=0;
  for(int i=0;i<17;i++) {
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
    uint64_t d=(v[c.out][k]^goal[k])&care[k];
    int pc=__builtin_popcountll(d);
    r+=pc; s+=pc+8*__builtin_popcountll(d&low[k])+4*__builtin_popcountll(d&negative[k]);
  }
  s+=nn>1?25*(nn-1):0;
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
vector<vector<Gate>> templates;
Circ seed(int templ) {
  auto gs=templates[templ];
  while(gs.size()>17) {
    int d=rr(gs.size()-1),r=rr(10+d);
    auto map=[&](int x) { return x==d+10?r:x>d+10?x-1:x; };
    vector<Gate> next;
    for(int i=0;i<(int)gs.size();i++) if(i!=d) {
      auto g=gs[i];g.a=map(g.a);g.b=map(g.b);next.push_back(g);
    }
    gs=next;
  }
  Circ c;copy(gs.begin(),gs.end(),c.g.begin());return c;
}
void mutate(Circ& c) {
  int i=rr(17),t=rr(100);
  auto& g=c.g[i];
  if(t<41) g.a=rr(10+i);
  else if(t<82) g.b=rr(10+i);
  else if(t<96) { int z=rr(100); g.op=z<42?0:z<84?1:z<98?2:z==98?3:4; }
  else if(t<99) {g.a=rr(10+i);g.b=rr(10+i);}
  else c.out=10+rr(17);
}
int main(int argc,char**argv) {
  int seconds=argc>1?atoi(argv[1]):300;
  ifstream sf("/tmp/oec/pequalnp-pilot-92/local1886-care-templates.txt");
  int tcount;sf>>tcount;
  for(int i=0;i<tcount;i++) {int n;sf>>n;vector<Gate> gs(n);for(auto &g:gs)sf>>g.op>>g.a>>g.b;templates.push_back(gs);}
  if(!sf) {cerr<<"invalid templates"<<endl;return 2;}
  rng.seed(argc>2?strtoull(argv[2],nullptr,10):17);
  const int edges[15][2]={{0,1},{1,2},{2,3},{3,4},{4,0},{0,5},{1,6},{2,7},{3,8},{4,9},{5,7},{7,9},{9,6},{6,8},{8,5}};
  for(int x=0;x<1024;x++) {
    uint64_t bit=uint64_t(1)<<(x%64);int k=x/64;
    for(int i=0;i<10;i++) if(x>>i&1)base[i][k]|=bit;
    bool f=false;for(auto e:edges)f|=(x>>e[0]&1)&&(x>>e[1]&1);
    if(f)goal[k]|=bit;else negative[k]|=bit;
    if((x&3)!=3)care[k]|=bit;
    if(__builtin_popcount((unsigned)x)<=3)low[k]|=bit;
  }
  vector<pair<int,Circ>> seeds;
  int best=100000;Circ champion;
  for(int t=0;t<(int)templates.size();t++)for(int z=0;z<500;z++) {
    Circ c=seed(t);int s=score(c);seeds.push_back({s,c});
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
        dump(c,s,"/tmp/oec/pequalnp-pilot-92/local1886-care-best.txt");
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
  dump(champion,best,"/tmp/oec/pequalnp-pilot-92/local1886-care-best.txt");
  return best==0?0:1;
}
