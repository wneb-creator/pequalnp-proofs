#include <array>
#include <random>
#include <algorithm>
#include <fstream>
#include <iostream>
#include <chrono>
#include <cmath>
#include <cstdint>
using TT=unsigned __int128;
struct Gate{int op,a,b;};
struct Circuit{std::array<Gate,13> g;};
std::array<TT,20> init;std::array<TT,4> target;
std::mt19937_64 rng;int R(int n){return rng()%n;}
std::array<int,4> outputs;
int pc(TT x){return __builtin_popcountll((uint64_t)x)+__builtin_popcountll((uint64_t)(x>>64));}
int eval(const Circuit &c,bool output=false){
 auto w=init;int nots=0;
 for(int j=0;j<13;j++){auto g=c.g[j];w[7+j]=g.op==0?(w[g.a]&w[g.b]):g.op==1?(w[g.a]|w[g.b]):~w[g.a];nots+=g.op==2;}
 int e=0;std::array<int,4> out;
 for(int t=0;t<4;t++){int best=129,bw=0;for(int j=0;j<20;j++){int d=pc((w[j]^target[t]) & (t==3?~TT(0):~target[3]));if(d<best){best=d;bw=j;}}e+=best;out[t]=bw;}
 bool active[20]={};for(int o:out)active[o]=true;bool activeNot=false;
 for(int j=12;j>=0;j--)if(active[7+j]){auto g=c.g[j];active[g.a]=true;if(g.op!=2)active[g.b]=true;else activeNot=true;}
 if(output)outputs=out;
 if(nots==0||!activeNot)e+=20;
 return e;
}
void save(const Circuit&c,int err,uint64_t steps,const std::string &path){
 eval(c,true);std::ofstream f(path);f<<"errors "<<err<<" steps "<<steps<<"\n";
 for(int j=0;j<13;j++)f<<j<<" "<<c.g[j].op<<" "<<c.g[j].a<<" "<<c.g[j].b<<"\n";
 f<<"outputs";for(int o:outputs)f<<" "<<o;f<<"\n";
}
Circuit seed(){
 Circuit c;
 for(int j=0;j<13;j++)c.g[j]={R(2),R(j+7),R(j+7)};
 if(R(3)){
  std::array<std::array<int,3>,3> trip={{{0,1,3},{0,2,6},{0,4,5}}};std::shuffle(trip.begin(),trip.end(),rng);
  for(int j=0;j<3;j++){std::shuffle(trip[j].begin(),trip[j].end(),rng);c.g[2*j]={1,trip[j][0],trip[j][1]};c.g[2*j+1]={1,7+2*j,trip[j][2]};}
  // Six-cycle starts from a three-star cover but omits one combining gate.
  c.g[6]={1,2,4};c.g[7]={0,1,13};c.g[8]={1,2,3};c.g[9]={0,5,15};c.g[10]={1,3,4};c.g[11]={0,6,17};c.g[12]={1,14,16};
 }
 c.g[R(13)].op=2;return c;
}
int main(int argc,char**argv){
 int seconds=argc>1?std::stoi(argv[1]):300,seedn=argc>2?std::stoi(argv[2]):1;std::string path=argc>3?argv[3]:"bestcycle.txt";rng.seed(seedn);
 for(int x=0;x<128;x++)for(int j=0;j<7;j++)if(x>>j&1)init[j]|=TT(1)<<x;
 target[0]=init[0]|init[1]|init[3];target[1]=init[0]|init[2]|init[6];target[2]=init[0]|init[4]|init[5];
 target[3]=(init[1]&init[2])|(init[2]&init[5])|(init[5]&init[3])|(init[3]&init[6])|(init[6]&init[4])|(init[4]&init[1]);
 int best=1000;uint64_t steps=0,runs=0;auto t0=std::chrono::steady_clock::now();
 while(std::chrono::duration<double>(std::chrono::steady_clock::now()-t0).count()<seconds){
  Circuit c=seed();int cost=eval(c);runs++;
  for(int epoch=0;epoch<50;epoch++)for(int it=0;it<10000;it++){
   Circuit next=c;int edits=1+(R(100)<12)+(R(100)<2);
   for(int e=0;e<edits;e++){int j=R(13),type=R(5);auto &g=next.g[j];if(type==0)g.op=R(3);else if(type<=2)g.a=R(7+j);else g.b=R(7+j);}
   int nc=eval(next);steps++;double temp=0.15+1.6*std::pow(1.0-epoch/50.0,3);bool accept=nc<=cost||std::generate_canonical<double,64>(rng)<std::exp((cost-nc)/temp);
   if(accept){c=next;cost=nc;}
   if(nc<best){best=nc;save(next,best,steps,path);std::cout<<"best "<<best<<" steps "<<steps<<" runs "<<runs<<" elapsed "<<std::chrono::duration<double>(std::chrono::steady_clock::now()-t0).count()<<std::endl;}
   if(nc==0)return 0;
   if(steps%100000==0&&std::chrono::duration<double>(std::chrono::steady_clock::now()-t0).count()>seconds)goto done;
  }
 }
 done:std::cout<<"END best "<<best<<" steps "<<steps<<" runs "<<runs<<std::endl;
}
