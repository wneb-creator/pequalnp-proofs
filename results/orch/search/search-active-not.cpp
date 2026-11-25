#include <array>
#include <vector>
#include <fstream>
#include <iostream>
#include <random>
#include <chrono>
#include <cmath>
#include <bit>
using namespace std;
struct Gate { int op,a,b; };
using TT=array<uint64_t,16>;
using Circuit=array<Gate,19>;
mt19937_64 rng;
array<TT,10> inputs;
TT target,critical;
vector<array<Gate,20>> seeds;
uint64_t evaluations=0;
int score(const Circuit &c,int mode,int *plain=nullptr) {
 array<TT,29> w;
 for(int i=0;i<10;i++)w[i]=inputs[i];
 int nn=0;
 for(int i=0;i<19;i++) {
  auto g=c[i];
  if(g.op==0) for(int k=0;k<16;k++)w[10+i][k]=w[g.a][k]&w[g.b][k];
  if(g.op==1) for(int k=0;k<16;k++)w[10+i][k]=w[g.a][k]|w[g.b][k];
  if(g.op==2) { nn++;for(int k=0;k<16;k++)w[10+i][k]=~w[g.a][k]; }
 }
 int s=0,p=0;
 for(int k=0;k<16;k++) {
  auto e=w[28][k]^target[k];p+=popcount(e);
  s+=popcount(e);
  if(mode==1)s+=4*popcount(e&critical[k]);
  if(mode==2)s+=3*popcount(e&~target[k]);
 }
 bool active[29]={}; active[28]=true; int an=0;
 for(int i=18;i>=0;i--)if(active[10+i]) { active[c[i].a]=true; if(c[i].op!=2)active[c[i].b]=true; else an++; }
 if(an==0)s+=20; if(an>4)s+=20*(an-4);
 if(plain)*plain=p;
 evaluations++;
 return s;
}
Circuit initial() {
 Circuit c;
 auto s=seeds[rng()%seeds.size()];
 int drop=rng()%20;
 int replacement=(rng()%2?s[drop].a:s[drop].b);
 if(drop==19) {drop=18;replacement=s[drop].a;}
 for(int i=0,j=0;i<20;i++)if(i!=drop) {
  auto g=s[i];
  auto remap=[&](int v){if(v==10+drop)v=replacement;return v>10+drop?v-1:v;};
  g.a=remap(g.a);g.b=remap(g.b);c[j++]=g;
 }
 return c;
}
void print(const Circuit &c,int s,int p) {
 cerr<<"score "<<s<<" errors "<<p<<" evaluations "<<evaluations<<"\n";
 for(int i=0;i<19;i++)cerr<<10+i<<" "<<c[i].op<<" "<<c[i].a<<" "<<c[i].b<<"\n";
 cerr.flush();
}
int main(int argc,char **argv) {
 if(argc!=4)return 2;
 rng.seed(stoull(argv[1]));int seconds=stoi(argv[2]);
 ifstream in(argv[3]);int ns;in>>ns;seeds.resize(ns);
 for(auto &s:seeds)for(auto &g:s)in>>g.op>>g.a>>g.b;
 vector<pair<int,int>> edges={{0,1},{1,2},{2,3},{3,4},{4,0},{0,5},{1,6},{2,7},{3,8},{4,9},{5,7},{7,9},{9,6},{6,8},{8,5}};
 for(int r=0;r<1024;r++) {
  for(int i=0;i<10;i++)if((r>>i)&1)inputs[i][r/64]|=1ull<<(r%64);
  bool t=false;for(auto [u,v]:edges)if((r>>u&1)&&(r>>v&1))t=true;
  if(t)target[r/64]|=1ull<<(r%64);
  bool crit=t&&popcount((unsigned)r)==2;
  if(!t) {crit=true;for(int i=0;i<10;i++)if(!(r>>i&1)) {
   int q=r|(1<<i);bool qt=false;for(auto [u,v]:edges)if((q>>u&1)&&(q>>v&1))qt=true;
   if(!qt)crit=false;
  }}
  if(crit)critical[r/64]|=1ull<<(r%64);
 }
 auto start=chrono::steady_clock::now();int best=10000;uint64_t runs=0;
 while(chrono::duration<double>(chrono::steady_clock::now()-start).count()<seconds) {
  int mode=runs%3;Circuit c=initial();int s=score(c,mode);
  for(int j=0;j<100000;j++) {
   int i=rng()%19;Gate old=c[i];auto &g=c[i];
   int mut=rng()%6;
   if(mut==0)g.op=rng()%3;
   if(mut==1)g.a=rng()%(10+i);
   if(mut==2)g.b=rng()%(10+i);
   if(mut==3){g.a=rng()%(10+i);g.b=rng()%(10+i);}
   if(mut==4){g.op=rng()%3;g.a=rng()%(10+i);}
   if(mut==5){g.op=rng()%3;g.a=rng()%(10+i);g.b=rng()%(10+i);}
   int plain=0,ns=score(c,mode,&plain);
   if(plain<best){best=plain;print(c,ns,plain);}
   if(!plain){cout<<"FOUND\n";for(auto g:c)cout<<g.op<<" "<<g.a<<" "<<g.b<<"\n";return 0;}
   double temp=0.1+5.0*(1.0-(j%50000)/50000.0);
   bool take=ns<=s || generate_canonical<double,53>(rng)<exp((s-ns)/temp);
   if(take)s=ns;else c[i]=old;
  }
  runs++;
  if(runs%100==0)cerr<<"progress runs="<<runs<<" best="<<best<<" evals="<<evaluations<<"\n";
 }
 cerr<<"FINISHED runs="<<runs<<" best="<<best<<" evals="<<evaluations<<"\n";
}
