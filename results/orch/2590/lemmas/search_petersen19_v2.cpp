#include <array>
#include <vector>
#include <random>
#include <algorithm>
#include <chrono>
#include <iostream>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <csignal>
using namespace std;
struct Gate{int op,a,b;};
using Circ=array<Gate,19>;
const array<pair<int,int>,15> E={{{0,1},{1,2},{2,3},{3,4},{4,0},{0,5},{1,6},{2,7},{3,8},{4,9},{5,7},{7,9},{9,6},{6,8},{8,5}}};
const array<uint64_t,10> inputs={1361186ULL,2208273ULL,4409482ULL,17437748ULL,135004873ULL,42997773ULL,337641582ULL,549454704ULL,117465984ULL,939555840ULL};
const uint64_t goal=1073709056ULL;
const array<array<int,10>,120> automorphisms={{{{0,1,2,3,4,5,6,7,8,9}},{{0,1,2,7,5,4,6,3,9,8}},{{0,1,6,8,5,4,2,9,3,7}},{{0,1,6,9,4,5,2,8,7,3}},{{0,4,3,2,1,5,9,8,7,6}},{{0,4,3,8,5,1,9,2,6,7}},{{0,4,9,6,1,5,3,7,8,2}},{{0,4,9,7,5,1,3,6,2,8}},{{0,5,7,2,1,4,8,9,3,6}},{{0,5,7,9,4,1,8,2,6,3}},{{0,5,8,3,4,1,7,6,2,9}},{{0,5,8,6,1,4,7,3,9,2}},{{1,0,4,3,2,6,5,9,8,7}},{{1,0,4,9,6,2,5,3,7,8}},{{1,0,5,7,2,6,4,8,9,3}},{{1,0,5,8,6,2,4,7,3,9}},{{1,2,3,4,0,6,7,8,9,5}},{{1,2,3,8,6,0,7,4,5,9}},{{1,2,7,5,0,6,3,9,8,4}},{{1,2,7,9,6,0,3,5,4,8}},{{1,6,8,3,2,0,9,5,4,7}},{{1,6,8,5,0,2,9,3,7,4}},{{1,6,9,4,0,2,8,7,3,5}},{{1,6,9,7,2,0,8,4,5,3}},{{2,1,0,4,3,7,6,5,9,8}},{{2,1,0,5,7,3,6,4,8,9}},{{2,1,6,8,3,7,0,9,5,4}},{{2,1,6,9,7,3,0,8,4,5}},{{2,3,4,0,1,7,8,9,5,6}},{{2,3,4,9,7,1,8,0,6,5}},{{2,3,8,5,7,1,4,6,0,9}},{{2,3,8,6,1,7,4,5,9,0}},{{2,7,5,0,1,3,9,8,4,6}},{{2,7,5,8,3,1,9,0,6,4}},{{2,7,9,4,3,1,5,6,0,8}},{{2,7,9,6,1,3,5,4,8,0}},{{3,2,1,0,4,8,7,6,5,9}},{{3,2,1,6,8,4,7,0,9,5}},{{3,2,7,5,8,4,1,9,0,6}},{{3,2,7,9,4,8,1,5,6,0}},{{3,4,0,1,2,8,9,5,6,7}},{{3,4,0,5,8,2,9,1,7,6}},{{3,4,9,6,8,2,0,7,1,5}},{{3,4,9,7,2,8,0,6,5,1}},{{3,8,5,0,4,2,6,7,1,9}},{{3,8,5,7,2,4,6,0,9,1}},{{3,8,6,1,2,4,5,9,0,7}},{{3,8,6,9,4,2,5,1,7,0}},{{4,0,1,2,3,9,5,6,7,8}},{{4,0,1,6,9,3,5,2,8,7}},{{4,0,5,7,9,3,1,8,2,6}},{{4,0,5,8,3,9,1,7,6,2}},{{4,3,2,1,0,9,8,7,6,5}},{{4,3,2,7,9,0,8,1,5,6}},{{4,3,8,5,0,9,2,6,7,1}},{{4,3,8,6,9,0,2,5,1,7}},{{4,9,6,1,0,3,7,8,2,5}},{{4,9,6,8,3,0,7,1,5,2}},{{4,9,7,2,3,0,6,5,1,8}},{{4,9,7,5,0,3,6,2,8,1}},{{5,0,1,2,7,8,4,6,3,9}},{{5,0,1,6,8,7,4,2,9,3}},{{5,0,4,3,8,7,1,9,2,6}},{{5,0,4,9,7,8,1,3,6,2}},{{5,7,2,1,0,8,9,3,6,4}},{{5,7,2,3,8,0,9,1,4,6}},{{5,7,9,4,0,8,2,6,3,1}},{{5,7,9,6,8,0,2,4,1,3}},{{5,8,3,2,7,0,6,4,1,9}},{{5,8,3,4,0,7,6,2,9,1}},{{5,8,6,1,0,7,3,9,2,4}},{{5,8,6,9,7,0,3,1,4,2}},{{6,1,0,4,9,8,2,5,3,7}},{{6,1,0,5,8,9,2,4,7,3}},{{6,1,2,3,8,9,0,7,4,5}},{{6,1,2,7,9,8,0,3,5,4}},{{6,8,3,2,1,9,5,4,7,0}},{{6,8,3,4,9,1,5,2,0,7}},{{6,8,5,0,1,9,3,7,4,2}},{{6,8,5,7,9,1,3,0,2,4}},{{6,9,4,0,1,8,7,3,5,2}},{{6,9,4,3,8,1,7,0,2,5}},{{6,9,7,2,1,8,4,5,3,0}},{{6,9,7,5,8,1,4,2,0,3}},{{7,2,1,0,5,9,3,6,4,8}},{{7,2,1,6,9,5,3,0,8,4}},{{7,2,3,4,9,5,1,8,0,6}},{{7,2,3,8,5,9,1,4,6,0}},{{7,5,0,1,2,9,8,4,6,3}},{{7,5,0,4,9,2,8,1,3,6}},{{7,5,8,3,2,9,0,6,4,1}},{{7,5,8,6,9,2,0,3,1,4}},{{7,9,4,0,5,2,6,3,1,8}},{{7,9,4,3,2,5,6,0,8,1}},{{7,9,6,1,2,5,4,8,0,3}},{{7,9,6,8,5,2,4,1,3,0}},{{8,3,2,1,6,5,4,7,0,9}},{{8,3,2,7,5,6,4,1,9,0}},{{8,3,4,0,5,6,2,9,1,7}},{{8,3,4,9,6,5,2,0,7,1}},{{8,5,0,1,6,3,7,4,2,9}},{{8,5,0,4,3,6,7,1,9,2}},{{8,5,7,2,3,6,0,9,1,4}},{{8,5,7,9,6,3,0,2,4,1}},{{8,6,1,0,5,3,9,2,4,7}},{{8,6,1,2,3,5,9,0,7,4}},{{8,6,9,4,3,5,1,7,0,2}},{{8,6,9,7,5,3,1,4,2,0}},{{9,4,0,1,6,7,3,5,2,8}},{{9,4,0,5,7,6,3,1,8,2}},{{9,4,3,2,7,6,0,8,1,5}},{{9,4,3,8,6,7,0,2,5,1}},{{9,6,1,0,4,7,8,2,5,3}},{{9,6,1,2,7,4,8,0,3,5}},{{9,6,8,3,4,7,1,5,2,0}},{{9,6,8,5,7,4,1,3,0,2}},{{9,7,2,1,6,4,5,3,0,8}},{{9,7,2,3,4,6,5,1,8,0}},{{9,7,5,0,4,6,2,8,1,3}},{{9,7,5,8,6,4,2,0,3,1}}}};
mt19937_64 gen;
uint64_t evaluations=0;
volatile sig_atomic_t stopped=0;
void stop_handler(int){stopped=1;}
int rnd(int n){return gen()%n;}
double unit(){return double(gen()>>11)*0x1.0p-53;}
struct Score{int fp,fn;int value(int weight)const{return fp*weight+fn;}};
Score eval(const Circ& c){
 array<uint64_t,29>w;
 for(int i=0;i<10;i++)w[i]=inputs[i];
 for(int i=0;i<19;i++){auto g=c[i];w[10+i]=g.op==0?w[g.a]&w[g.b]:w[g.a]|w[g.b];}
 evaluations++;
 return {__builtin_popcountll(w[28]&~goal),__builtin_popcountll(goal&~w[28])};
}
void print(const Circ& c,Score s){
 cout<<"score fp="<<s.fp<<" fn="<<s.fn<<" evaluations="<<evaluations<<"\n";
 for(int i=0;i<19;i++)cout<<10+i<<" "<<c[i].op<<" "<<c[i].a<<" "<<c[i].b<<"\n";
 cout.flush();
}
Circ seed(){
 vector<int> independent;
 while(true){
  int m=rnd(1024);
  if(__builtin_popcount((unsigned)m)!=4)continue;
  bool good=true;
  for(auto [a,b]:E)if((m>>a&1)&&(m>>b&1))good=false;
  if(good){for(int a=0;a<10;a++)if(m>>a&1)independent.push_back(a);break;}
 }
 array<vector<int>,10> stars;
 for(auto [a,b]:E){
  bool ca=find(independent.begin(),independent.end(),a)==independent.end();
  bool cb=find(independent.begin(),independent.end(),b)==independent.end();
  if(ca&&cb){if(rnd(2))swap(a,b);}
  else if(cb)swap(a,b);
  stars[a].push_back(b);
 }
 vector<Gate> c;
 vector<int> outputs,centers;
 for(int a=0;a<10;a++)if(!stars[a].empty())centers.push_back(a);
 shuffle(centers.begin(),centers.end(),gen);
 for(int a:centers){
  auto ns=stars[a]; shuffle(ns.begin(),ns.end(),gen);
  int out=ns[0];
  for(size_t j=1;j<ns.size();j++){c.push_back({1,out,ns[j]});out=9+c.size();}
  c.push_back({0,a,out});outputs.push_back(9+c.size());
 }
 shuffle(outputs.begin(),outputs.end(),gen);
 while(outputs.size()>1){
  int a=outputs.back();outputs.pop_back();int b=outputs.back();outputs.pop_back();
  c.push_back({1,a,b});outputs.push_back(9+c.size());
 }
 if(c.size()!=20){cerr<<"bad seed "<<c.size()<<"\n";exit(2);}
 if(rnd(2)) c={
  {1,9,5},{1,0,9},{1,0,6},{1,7,3},{0,1,12},{1,6,5},{1,11,3},
  {1,13,1},{1,14,2},{0,12,15},{0,4,16},{0,19,11},{1,7,21},
  {0,18,17},{1,20,23},{1,3,15},{0,25,8},{0,22,10},{1,27,26},{1,24,28}
 };
 if(rnd(2)){
  c.clear();vector<int> coreouts;vector<pair<int,int>> pairs;
  auto inI=[&](int v){return find(independent.begin(),independent.end(),v)!=independent.end();};
  for(auto [a,b]:E)if(!inI(a)&&!inI(b))pairs.push_back({a,b});
  shuffle(pairs.begin(),pairs.end(),gen);
  auto gate=[&](int op,int a,int b){c.push_back({op,a,b});return 9+int(c.size());};
  for(auto [aa,bb]:pairs){
   int a=aa,b=bb;if(rnd(2))swap(a,b);vector<int>na,nb;
   for(auto [u,v]:E){if(u==a&&v!=b)na.push_back(v);if(v==a&&u!=b)na.push_back(u);if(u==b&&v!=a)nb.push_back(v);if(v==b&&u!=a)nb.push_back(u);}
   if(na.size()!=2||nb.size()!=2)abort();
   int ob=gate(1,nb[0],nb[1]),ab=gate(0,b,ob),left=gate(1,a,ab);
   int oa=gate(1,na[0],na[1]),right=gate(1,b,oa);coreouts.push_back(gate(0,left,right));
  }
  while(coreouts.size()>1){int a=coreouts.back();coreouts.pop_back();int b=coreouts.back();coreouts.pop_back();coreouts.push_back(gate(1,a,b));}
  if(c.size()!=20)abort();
 }
 int gone=rnd(20);
 int replacement=rnd(2)?c[gone].a:c[gone].b;
 Circ out;
 for(int i=0,j=0;i<20;i++)if(i!=gone){
  auto g=c[i];
  auto remap=[&](int x){if(x==10+gone)x=replacement;return x>10+gone?x-1:x;};
  out[j++]={g.op,remap(g.a),remap(g.b)};
 }

 if(rnd(3)==0){
  const array<Gate,18> approx={{{1,2,9},{1,10,5},{1,9,3},{1,0,6},{1,3,5},{1,6,14},{1,0,12},{1,13,2},{0,17,15},{0,4,16},{0,18,16},{1,7,20},{0,17,1},{1,19,22},{0,15,8},{0,21,11},{1,25,24},{1,23,26}}};
  for(int i=0;i<18;i++)out[i]=approx[i];
  out[18]={1,27,27};
 }
 const auto& p=automorphisms[rnd(automorphisms.size())];
 for(auto& g:out){if(g.a<10)g.a=p[g.a];if(g.b<10)g.b=p[g.b];}
 return out;
}
int main(int argc,char**argv){
 int seconds=argc>1?atoi(argv[1]):600;
 uint64_t seednum=argc>2?strtoull(argv[2],nullptr,10):2590;
 gen.seed(seednum);signal(SIGTERM,stop_handler);signal(SIGINT,stop_handler);
 cout<<"seed="<<seednum<<" duration="<<seconds<<" inputs=10 gates=19 critical_rows=30 ops=AND_OR_only\n";
 auto start=chrono::steady_clock::now();double nextlog=30;
 int best=1000;uint64_t rounds=0;
 while(!stopped&&chrono::duration<double>(chrono::steady_clock::now()-start).count()<seconds){
  Circ c=seed();Score sc=eval(c);int weight=1+rnd(8),cost=sc.value(weight);
  for(int i=0;i<100000&&!stopped;i++){
   Circ d=c;int changes=rnd(12)==0?2+rnd(4):1;
   for(int z=0;z<changes;z++){
    int j=rnd(19),what=rnd(3);
    if(what==0)d[j].op=rnd(2);
    else if(what==1)d[j].a=rnd(10+j);
    else d[j].b=rnd(10+j);
   }
   Score sd=eval(d);int newcost=sd.value(weight);
   double temp=(i%20000<1000)?0.4:0.04;
   if(newcost<=cost||unit()<exp(double(cost-newcost)/temp)){c=d;cost=newcost;sc=sd;}
   if(sd.fp+sd.fn<best){best=sd.fp+sd.fn;print(d,sd);}
   if(sd.fp==0&&sd.fn==0){cout<<"FOUND\n";print(d,sd);return 0;}
   if(i%1000==0){
    double elapsed=chrono::duration<double>(chrono::steady_clock::now()-start).count();
    if(elapsed>=nextlog){cout<<"PROGRESS elapsed="<<elapsed<<" evaluations="<<evaluations<<" best="<<best<<"\n";cout.flush();nextlog+=30;}
    if(elapsed>=seconds)break;
   }
  }
  rounds++;
 }
 cout<<"DONE stopped="<<stopped<<" rounds="<<rounds<<" evaluations="<<evaluations<<" best_critical_errors="<<best<<"\n";
}
