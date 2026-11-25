#include <algorithm>
#include <array>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <random>
#include <vector>
using namespace std;
struct G { int a,b; bool op; };
using C=array<G,26>;
array<uint64_t,14> inputs;
uint64_t target=0;
vector<pair<int,int>> edges;
mt19937_64 rng(2583148);
int score(const C& c) {
 uint64_t v[40]; for(int i=0;i<14;i++)v[i]=inputs[i];
 for(int i=0;i<26;i++)v[14+i]=c[i].op?(v[c[i].a]|v[c[i].b]):(v[c[i].a]&v[c[i].b]);
 return __builtin_popcountll(v[39]^target);
}
C initial() {
 vector<G> c;
 vector<int> outs;
 vector<int> perm{0,1,2,3,4,5,6}; shuffle(perm.begin(),perm.end(),rng);
 for(int j:perm){
  vector<int> pts;for(auto [p,l]:edges)if(l==j)pts.push_back(p);
  shuffle(pts.begin(),pts.end(),rng);
  int r=14+c.size();c.push_back({pts[0],pts[1],true});
  int s=14+c.size();c.push_back({r,pts[2],true});
  outs.push_back(14+c.size());c.push_back({s,7+j,false});
 }
 shuffle(outs.begin(),outs.end(),rng);
 int r=outs[0];for(int i=1;i<7;i++){int s=14+c.size();c.push_back({r,outs[i],true});r=s;}
 int del=3*(rng()%7)+1, rep=c[del].a;
 C out;int k=0;
 for(int i=0;i<27;i++)if(i!=del){
  G g=c[i];auto fix=[&](int x){if(x==14+del)x=rep;if(x>14+del)x--;return x;};
  g.a=fix(g.a);g.b=fix(g.b);out[k++]=g;
 }
 return out;
}
int main(int argc,char**argv){
 int seconds=argc>1?atoi(argv[1]):900;
 vector<int> tests;
 for(int i=0;i<7;i++)for(int j=0;j<7;j++)if(__builtin_popcount((i+1)&(j+1))%2==0){edges.push_back({i,j});tests.push_back((1<<i)|(1<<(7+j)));}
 target=(uint64_t(1)<<tests.size())-1;
 for(int s=0;s<128;s++){
  int t=127;for(auto [p,l]:edges)if(s>>p&1)t&=~(1<<l);
  int s2=127;for(auto [p,l]:edges)if(t>>l&1)s2&=~(1<<p);
  if(s==s2)tests.push_back(s|(t<<7));
 }
 for(int i=0;i<14;i++)for(int t=0;t<(int)tests.size();t++)if(tests[t]>>i&1)inputs[i]|=uint64_t(1)<<t;
 cout<<"Exact monotone test set: "<<edges.size()<<" edge minterms, "<<tests.size()-edges.size()<<" maximal independent sets\n"<<flush;
 auto start=chrono::steady_clock::now();uint64_t trials=0,restarts=0;int best=100;C bestc;
 uniform_real_distribution<double> unif(0,1);
 for(;;){
  C c=initial();int sc=score(c);double temp=0.0;restarts++;
  for(int it=0;it<1000000;it++){
   C d=c;int mut=1+(rng()%100<40?1:0)+(rng()%100<15?2:0);
   for(int m=0;m<mut;m++){int g=rng()%26,t=rng()%5;if(t==0)d[g].op=!d[g].op;else if(t<3)d[g].a=rng()%(14+g);else d[g].b=rng()%(14+g);}
   int sd=score(d);trials++;
   if(sd<=sc){c=d;sc=sd;}
   if(sd<best){best=sd;bestc=d;cout<<"best="<<best<<" trials="<<trials<<" restarts="<<restarts<<" seconds="<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<"\n"<<flush;}
   if(sd==0){cout<<"FOUND\n";for(auto g:d)cout<<(g.op?"or":"and")<<' '<<g.a<<' '<<g.b<<'\n';return 0;}
  }
  double elapsed=chrono::duration<double>(chrono::steady_clock::now()-start).count();
  if(restarts%100==0)cout<<"progress trials="<<trials<<" restarts="<<restarts<<" best="<<best<<" seconds="<<elapsed<<"\n"<<flush;
  if(elapsed>=seconds){cout<<"DONE trials="<<trials<<" restarts="<<restarts<<" best="<<best<<" seconds="<<elapsed<<"\n";for(auto g:bestc)cout<<(g.op?"or":"and")<<' '<<g.a<<' '<<g.b<<'\n';return 1;}
 }
}
