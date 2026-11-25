#include <array>
#include <vector>
#include <random>
#include <chrono>
#include <iostream>
#include <cmath>
#include <cstdint>
#include <algorithm>
using namespace std;
struct Gate { int op,a,b; };
using Net=array<Gate,11>;
array<uint64_t,6> raw;
array<uint64_t,4> ts;
uint64_t mat;
mt19937_64 rng(1092592);
int randn(int n){return rng()%n;}
struct Result {int score;array<int,5> outs;};
Result eval(const Net& net){
 array<uint64_t,17> w{};copy(raw.begin(),raw.end(),w.begin());
 for(int g=0;g<11;g++){
  auto n=net[g];uint64_t a=n.a<6+g?w[n.a]:0,b=n.b<6+g?w[n.b]:0;
  w[6+g]=n.op==0?a&b:n.op==1?a|b:~a;
 }
 Result r{0,{}};
 for(int t=0;t<5;t++){
  int best=100,ind=-1;
  for(int i=0;i<17;i++){
   int d=__builtin_popcountll(t<4?w[i]^ts[t]:(w[i]&ts[3])^mat);
   if(d<best){best=d;ind=i;}
  }
  r.score+=(t<4?4:1)*best;r.outs[t]=ind;
 }
 return r;
}
void show(const Net& n,const Result&r){
 cout<<"score "<<r.score<<" outputs [";
 for(int i=0;i<5;i++)cout<<(i?",":"")<<r.outs[i];
 cout<<"] gates [";
 for(int g=0;g<11;g++)cout<<(g?",":"")<<"["<<n[g].op<<","<<n[g].a<<","<<n[g].b<<"]";
 cout<<"]"<<endl;
}
Net seed(){return Net{{{1,0,2},{1,6,5},{1,1,3},{1,8,5},{1,2,3},{1,10,4},{1,0,1},{1,12,4},{0,7,9},{0,14,11},{2,0,0}}};}
int main(int argc,char**argv){
 int seconds=argc>1?atoi(argv[1]):300;
 for(int i=0;i<6;i++)for(int x=0;x<64;x++)raw[i]|=uint64_t((x>>i)&1)<<x;
 ts={raw[0]|raw[2]|raw[5],raw[1]|raw[3]|raw[5],raw[2]|raw[3]|raw[4],raw[0]|raw[1]|raw[4]};
 mat=(raw[0]&raw[3])|(raw[1]&raw[2])|(raw[4]&raw[5]);
 Net bestnet=seed();Result best=eval(bestnet);show(bestnet,best);
 vector<Net> pool{bestnet};
 auto start=chrono::steady_clock::now();long long iters=0;int restarts=0;
 while(chrono::duration<double>(chrono::steady_clock::now()-start).count()<seconds){
  Net n=pool[randn(pool.size())];int cur=eval(n).score;
  double hot=randn(5)?3.0:12.0;
  for(int it=0;it<12000;it++,iters++){
   Net q=n;int g=randn(11),kind=randn(10);
   if(kind==0){q[g].op=randn(3);int nn=0;for(auto t:q)nn+=t.op==2;if(nn==0 || nn>4)continue;}
   else if(kind<3){if(q[g].op!=2)q[g].op^=1;}
   else if(kind<7)q[g].a=randn(7+g);
   else q[g].b=randn(7+g);
   Result r=eval(q);double temp=hot*(1.0-double(it)/12000)+0.06;
   if(r.score<=cur || generate_canonical<double,53>(rng)<exp((cur-r.score)/temp)){n=q;cur=r.score;}
   if(r.score<best.score){best=r;bestnet=q;pool.clear();pool.push_back(q);show(bestnet,best);if(!best.score)return 0;}
   else if(r.score==best.score && randn(32)==0){if(pool.size()<64)pool.push_back(q);else pool[randn(64)]=q;}
  }
  restarts++;
 }
 cout<<"done iterations "<<iters<<" restarts "<<restarts<<endl;show(bestnet,best);
}
