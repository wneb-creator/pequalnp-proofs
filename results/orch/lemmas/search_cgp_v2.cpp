#include <array>
#include <vector>
#include <random>
#include <algorithm>
#include <chrono>
#include <iostream>
#include <cmath>
#include <cstdint>
#include <cstdlib>
using namespace std;
using Bits=array<uint64_t,16>;
struct Gate{int op,a,b;};
using Circ=array<Gate,19>;
const array<pair<int,int>,15> E={{{0,1},{1,2},{2,3},{3,4},{4,0},{0,5},{1,6},{2,7},{3,8},{4,9},{5,7},{7,9},{9,6},{6,8},{8,5}}};
array<Bits,10> inputs;
Bits goal;
mt19937_64 gen;
uint64_t tests=0;
int rnd(int n){return gen()%n;}
double unit(){return double(gen()>>11)*0x1.0p-53;}
struct Score {int fp,fn,nots; double value(int weight) const{return fp*weight+fn+(nots==0?2:0);} };
Score eval(const Circ& c){
 array<Bits,29> w;
 for(int i=0;i<10;i++)w[i]=inputs[i];
 int nots=0;
 for(int i=0;i<19;i++){
  auto g=c[i];
  nots+=g.op==2;
  for(int k=0;k<16;k++)w[10+i][k]=g.op==0?w[g.a][k]&w[g.b][k]:g.op==1?w[g.a][k]|w[g.b][k]:~w[g.a][k];
 }
 Score s{0,0,nots};
 for(int k=0;k<16;k++){
  s.fp+=__builtin_popcountll(w[28][k]&~goal[k]);
  s.fn+=__builtin_popcountll(goal[k]&~w[28][k]);
 }
 tests++;
 return s;
}
void print(const Circ& c,Score s){
 cout<<"score fp="<<s.fp<<" fn="<<s.fn<<" not="<<s.nots<<" tests="<<tests<<"\n";
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
 int gone=rnd(20);
 int replacement=rnd(2)?c[gone].a:c[gone].b;
 Circ out;
 for(int i=0,j=0;i<20;i++)if(i!=gone){
  auto g=c[i];
  auto remap=[&](int x){if(x==10+gone)x=replacement;return x>10+gone?x-1:x;};
  out[j++]={g.op,remap(g.a),remap(g.b)};
 }
 if(rnd(2)){int j=rnd(18);out[j]={2,rnd(10+j),rnd(10+j)};}
 return out;
}
int main(int argc,char**argv){
 int seconds=argc>1?atoi(argv[1]):600;
 uint64_t seednum=argc>2?strtoull(argv[2],nullptr,10):123456789;
 gen.seed(seednum);
 for(int x=0;x<1024;x++){
  for(int a=0;a<10;a++)if(x>>a&1)inputs[a][x/64]|=uint64_t(1)<<(x%64);
  bool f=false;for(auto [a,b]:E)if((x>>a&1)&&(x>>b&1))f=true;
  if(f)goal[x/64]|=uint64_t(1)<<(x%64);
 }
 cout<<"seed="<<seednum<<" duration="<<seconds<<"\n";
 auto start=chrono::steady_clock::now();
 int bestErrors=1024;double bestWeighted=100000;
 uint64_t rounds=0;
 while(chrono::duration<double>(chrono::steady_clock::now()-start).count()<seconds){
  Circ c=seed();Score sc=eval(c);
  int weight=1+2*rnd(7);
  double cost=sc.value(weight);
  int stall=0;
  for(int i=0;i<50000;i++){
   Circ d=c;
   int changes=rnd(12)==0?2+rnd(3):1;
   for(int z=0;z<changes;z++){
    int j=rnd(19),what=rnd(3);
    if(what==0)d[j].op=rnd(3);
    else if(what==1)d[j].a=rnd(10+j);
    else d[j].b=rnd(10+j);
   }
   Score sd=eval(d);double newcost=sd.value(weight);
   double temp=(i%10000<1000)?0.8:0.12;
   if(newcost<=cost||unit()<exp((cost-newcost)/temp)){c=d;cost=newcost;sc=sd;}
   if(sd.fp+sd.fn<bestErrors&&sd.nots){bestErrors=sd.fp+sd.fn;print(d,sd);}
   if(sd.fp==0&&sd.fn==0&&sd.nots){cout<<"FOUND\n";print(d,sd);return 0;}
   if(i%1000==0&&chrono::duration<double>(chrono::steady_clock::now()-start).count()>=seconds)break;
  }
  rounds++;
 }
 cout<<"DONE rounds="<<rounds<<" evaluations="<<tests<<" best_total_errors_with_not="<<bestErrors<<"\n";
}
