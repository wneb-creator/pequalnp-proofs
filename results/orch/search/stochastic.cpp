#include <array>
#include <vector>
#include <random>
#include <algorithm>
#include <fstream>
#include <iostream>
#include <chrono>
#include <cmath>
#include <cstdint>
using TT=std::array<uint64_t,16>;
struct Gate{int op,a,b;};
struct Circuit{std::array<Gate,19> g;};
std::array<TT,30> init;
TT target;
std::array<std::pair<int,int>,15> edges={{{0,1},{1,2},{2,3},{3,4},{4,0},{0,5},{1,6},{2,7},{3,8},{4,9},{5,7},{7,9},{9,6},{6,8},{8,5}}};
std::mt19937_64 rng;
int R(int n){return rng()%n;}
int eval(const Circuit &c){
 auto w=init;
 for(int j=0;j<19;j++){
  auto g=c.g[j];
  for(int k=0;k<16;k++)w[10+j][k]=g.op==0?(w[g.a][k]&w[g.b][k]):g.op==1?(w[g.a][k]|w[g.b][k]):~w[g.a][k];
 }
 int e=0;for(int k=0;k<16;k++)e+=__builtin_popcountll(w[28][k]^target[k]);
 return e;
}
void save(const Circuit&c,int err,uint64_t steps,const std::string &path){
 std::ofstream f(path);f<<"errors "<<err<<" steps "<<steps<<"\n";
 for(int j=0;j<19;j++)f<<j<<" "<<c.g[j].op<<" "<<c.g[j].a<<" "<<c.g[j].b<<"\n";
}
Circuit seed(){
 std::vector<int> covers;
 for(int mask=0;mask<1024;mask++)if(__builtin_popcount((unsigned)mask)==6){
  bool ok=true;for(auto [a,b]:edges)if(!((mask>>a&1)||(mask>>b&1)))ok=false;
  if(ok)covers.push_back(mask);
 }
 int cover=covers[R(covers.size())];std::array<std::vector<int>,10> neighbors;
 for(auto [a,b]:edges){if(!(cover>>a&1))std::swap(a,b);else if((cover>>b&1)&&R(2))std::swap(a,b);neighbors[a].push_back(b);}
 std::vector<int> order;for(int a=0;a<10;a++)if(!neighbors[a].empty())order.push_back(a);
 std::shuffle(order.begin(),order.end(),rng);
 std::vector<Gate> gs;std::vector<int> stars;
 for(int a:order){auto ns=neighbors[a];std::shuffle(ns.begin(),ns.end(),rng);int w=ns[0];for(size_t j=1;j<ns.size();j++){gs.push_back({1,w,ns[j]});w=9+gs.size();}gs.push_back({0,a,w});stars.push_back(9+gs.size());}
 std::shuffle(stars.begin(),stars.end(),rng);int w=stars[0];for(size_t j=1;j<stars.size();j++){gs.push_back({1,w,stars[j]});w=9+gs.size();}
 while(gs.size()>19){int del=R(gs.size()-1);Gate g=gs[del];int repl=R(2)?g.a:g.b;gs.erase(gs.begin()+del);for(auto &h:gs){for(int*p:{&h.a,&h.b}){if(*p==del+10)*p=repl;else if(*p>del+10)--*p;}}}
 while(gs.size()<19){gs.push_back({1,9+(int)gs.size(),R(10)});}
 Circuit c;for(int j=0;j<19;j++)c.g[j]=gs[j];
 // Half the runs begin close to a monotone optimum; the others insert a negation.
 if(R(2)){int j=R(18);c.g[j].op=2;}
 return c;
}
int main(int argc,char**argv){
 int seconds=argc>1?std::stoi(argv[1]):300;int seedn=argc>2?std::stoi(argv[2]):1;std::string path=argc>3?argv[3]:"best.txt";rng.seed(seedn);
 for(int x=0;x<1024;x++){for(int j=0;j<10;j++)if(x>>j&1)init[j][x/64]|=uint64_t(1)<<(x%64);bool y=false;for(auto [a,b]:edges)y|=(x>>a&1)&&(x>>b&1);if(y)target[x/64]|=uint64_t(1)<<(x%64);}
 int best=1025;uint64_t steps=0,runs=0;auto t0=std::chrono::steady_clock::now();
 while(std::chrono::duration<double>(std::chrono::steady_clock::now()-t0).count()<seconds){
  Circuit c=seed();int cost=eval(c);runs++;
  for(int epoch=0;epoch<30;epoch++)for(int it=0;it<10000;it++){
   Circuit next=c;int edits=1+(R(100)<12)+(R(100)<2);
   for(int e=0;e<edits;e++){int j=R(19),type=R(5);auto &g=next.g[j];if(type==0)g.op=R(3);else if(type<=2)g.a=R(10+j);else g.b=R(10+j);}
   int nc=eval(next);steps++;double temp=0.18+2.5*std::pow(1.0-epoch/30.0,2);bool accept=nc<=cost||std::generate_canonical<double,64>(rng)<std::exp((cost-nc)/temp);
   if(accept){c=next;cost=nc;}
   bool hasnot=false;for(auto g:next.g)hasnot|=g.op==2;
   if(nc<best&&hasnot){best=nc;save(next,best,steps,path);std::cout<<"best "<<best<<" steps "<<steps<<" runs "<<runs<<" elapsed "<<std::chrono::duration<double>(std::chrono::steady_clock::now()-t0).count()<<std::endl;}
   if(nc==0&&hasnot)return 0;
   if(steps%100000==0&&std::chrono::duration<double>(std::chrono::steady_clock::now()-t0).count()>seconds)goto done;
  }
 }
 done:std::cout<<"END best "<<best<<" steps "<<steps<<" runs "<<runs<<std::endl;
}
