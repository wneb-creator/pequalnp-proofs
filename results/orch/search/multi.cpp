#include <array>
#include <vector>
#include <random>
#include <algorithm>
#include <fstream>
#include <iostream>
#include <chrono>
#include <cmath>
#include <cstdint>
struct Gate{int op,a,b;};
struct Circuit{std::array<Gate,13> g;};
std::array<uint64_t,20> init;std::array<uint64_t,5> target;int ng=11;
std::mt19937_64 rng;int R(int n){return rng()%n;}
std::array<int,5> outputs;
int eval(const Circuit &c,bool output=false){
 auto w=init;int nots=0;
 for(int j=0;j<ng;j++){auto g=c.g[j];w[6+j]=g.op==0?(w[g.a]&w[g.b]):g.op==1?(w[g.a]|w[g.b]):~w[g.a];nots+=g.op==2;}
 int e=0;for(int t=0;t<5;t++){int best=65,bw=0;for(int j=0;j<6+ng;j++){int d=__builtin_popcountll(w[j]^target[t]);if(d<best){best=d;bw=j;}}e+=best;if(output)outputs[t]=bw;}
 if(nots==0)e+=20;return e;
}
void save(const Circuit&c,int err,uint64_t steps,const std::string &path){
 eval(c,true);std::ofstream f(path);f<<"errors "<<err<<" steps "<<steps<<"\n";
 for(int j=0;j<ng;j++)f<<j<<" "<<c.g[j].op<<" "<<c.g[j].a<<" "<<c.g[j].b<<"\n";
 f<<"outputs";for(int o:outputs)f<<" "<<o;f<<"\n";
}
Circuit seed(){
 Circuit c;
 for(int j=0;j<ng;j++)c.g[j]={R(2),R(j+6),R(j+6)};
 if(R(3)){
  std::array<std::array<int,3>,4> trip={{{1,2,4},{0,2,5},{0,3,4},{1,3,5}}};std::shuffle(trip.begin(),trip.end(),rng);
  for(int j=0;j<4;j++){std::shuffle(trip[j].begin(),trip[j].end(),rng);c.g[2*j]={1,trip[j][0],trip[j][1]};c.g[2*j+1]={1,6+2*j,trip[j][2]};}
  c.g[8]={0,7,9};c.g[9]={0,11,13};c.g[10]={0,14,15};
 }
 c.g[R(ng)].op=2;return c;
}
int main(int argc,char**argv){
 int seconds=argc>1?std::stoi(argv[1]):300,seedn=argc>2?std::stoi(argv[2]):1;std::string path=argc>3?argv[3]:"bestmulti.txt";ng=argc>4?std::stoi(argv[4]):11;rng.seed(seedn);
 for(int x=0;x<64;x++)for(int j=0;j<6;j++)if(x>>j&1)init[j]|=uint64_t(1)<<x;
 target[0]=init[1]|init[2]|init[4];target[1]=init[0]|init[2]|init[5];target[2]=init[0]|init[3]|init[4];target[3]=init[1]|init[3]|init[5];target[4]=(init[0]&init[1])|(init[2]&init[3])|(init[4]&init[5]);
 int best=1000;uint64_t steps=0,runs=0;auto t0=std::chrono::steady_clock::now();
 while(std::chrono::duration<double>(std::chrono::steady_clock::now()-t0).count()<seconds){
  Circuit c=seed();int cost=eval(c);runs++;
  for(int epoch=0;epoch<40;epoch++)for(int it=0;it<10000;it++){
   Circuit next=c;int edits=1+(R(100)<10)+(R(100)<2);
   for(int e=0;e<edits;e++){int j=R(ng),type=R(5);auto &g=next.g[j];if(type==0)g.op=R(3);else if(type<=2)g.a=R(6+j);else g.b=R(6+j);}
   int nc=eval(next);steps++;double temp=0.12+1.4*std::pow(1.0-epoch/40.0,3);bool accept=nc<=cost||std::generate_canonical<double,64>(rng)<std::exp((cost-nc)/temp);
   if(accept){c=next;cost=nc;}
   if(nc<best){best=nc;save(next,best,steps,path);std::cout<<"best "<<best<<" steps "<<steps<<" runs "<<runs<<" elapsed "<<std::chrono::duration<double>(std::chrono::steady_clock::now()-t0).count()<<std::endl;}
   if(nc==0)return 0;
   if(steps%100000==0&&std::chrono::duration<double>(std::chrono::steady_clock::now()-t0).count()>seconds)goto done;
  }
 }
 done:std::cout<<"END best "<<best<<" steps "<<steps<<" runs "<<runs<<std::endl;
}
