#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <vector>
constexpr int N=13, INPUTS=26, GATES=63, TESTS=1848, WORDS=29, POSCOUNT=1144;
struct Gate {int a,b; bool is_and;};
using Net=std::array<Gate,GATES>;
using Sig=std::array<uint64_t,WORDS>;
using Values=std::array<Sig,INPUTS+GATES>;
uint64_t state;
uint64_t rnd(){state^=state<<13;state^=state>>7;return state^=state<<17;}
int ri(int n){return rnd()%n;}
std::vector<uint32_t> tests;
Values base{};
Sig target{};
std::vector<Gate> fullseed(){
 std::vector<Gate> gs;std::vector<int> roots;
 std::array<int,N> order{};for(int i=0;i<N;++i)order[i]=i;
 for(int i=N-1;i>0;--i)std::swap(order[i],order[ri(i+1)]);
 bool dual=ri(2);
 for(int l:order){
  std::array<int,4> leaves{};int j=0;
  for(int d:{0,1,3,9})leaves[j++]=dual?(N+(l-d+N)%N):(l+d)%N;
  for(int i=3;i>0;--i)std::swap(leaves[i],leaves[ri(i+1)]);
  int v=leaves[0];
  for(int i=1;i<4;++i){gs.push_back({v,leaves[i],false});v=INPUTS+int(gs.size())-1;}
  gs.push_back({v,dual?l:N+l,true});roots.push_back(INPUTS+int(gs.size())-1);
 }
 while(roots.size()>1){
  int i=ri(roots.size()),a=roots[i];roots.erase(roots.begin()+i);
  i=ri(roots.size());int b=roots[i];roots.erase(roots.begin()+i);
  roots.push_back(INPUTS+gs.size());gs.push_back({a,b,false});
 }
 return gs;
}
Net seednet(){
 auto gs=fullseed();int rem=ri(GATES),replacement=ri(2)?gs[rem].a:gs[rem].b;
 auto rw=[&](int w){if(w==INPUTS+rem)w=replacement;return w>INPUTS+rem?w-1:w;};
 Net out{};int j=0;
 for(int i=0;i<GATES+1;++i)if(i!=rem)out[j++]={rw(gs[i].a),rw(gs[i].b),gs[i].is_and};
 return out;
}
int eval(const Net&gs,Values&w,int from=0){
 for(int i=from;i<GATES;++i){auto &g=gs[i];auto&a=w[g.a];auto&b=w[g.b];auto&o=w[INPUTS+i];
  if(g.is_and){for(int j=0;j<WORDS;++j)o[j]=a[j]&b[j];}
  else {for(int j=0;j<WORDS;++j)o[j]=a[j]|b[j];}
 }
 auto &o=w.back();int score=0;
 for(int j=0;j<WORDS;++j)score+=std::popcount(o[j]^target[j]);
 return score;
}
void save(const Net&gs,const char*path,int score,const Values&w){
 std::ofstream f(path);f<<"gates "<<GATES<<" score "<<score<<"\n";
 for(auto g:gs)f<<(g.is_and?"and":"or")<<" "<<g.a<<" "<<g.b<<"\n";
 f<<"failed_tests";for(int j=0;j<TESTS;++j)if(bool(w.back()[j/64]>>(j%64)&1)!=(j<POSCOUNT))f<<" "<<j;f<<"\n";
}
bool check_seed(){
 for(int k=0;k<100;++k){auto gs=fullseed();std::array<Sig,90>w{};
  for(int i=0;i<INPUTS;++i)w[i]=base[i];
  for(int i=0;i<64;++i)for(int j=0;j<WORDS;++j)w[INPUTS+i][j]=gs[i].is_and?(w[gs[i].a][j]&w[gs[i].b][j]):(w[gs[i].a][j]|w[gs[i].b][j]);
  for(int j=0;j<WORDS;++j)if(w.back()[j]!=target[j])return false;
 }return true;
}
int main(int argc,char**argv){
 if(argc!=6)return 2;int seconds=std::stoi(argv[1]),mode=std::stoi(argv[5]);state=std::stoull(argv[2]);
 std::ifstream f(argv[3]);uint32_t m;while(f>>m)tests.push_back(m);if(tests.size()!=TESTS)return 3;
 for(int i=0;i<INPUTS;++i)for(int j=0;j<TESTS;++j)if(tests[j]>>i&1)base[i][j/64]|=uint64_t(1)<<(j%64);
 for(int j=0;j<POSCOUNT;++j)target[j/64]|=uint64_t(1)<<(j%64);
 if(!check_seed()){std::cerr<<"baseline check failed\n";return 4;}
 std::cout<<"64_gate_baseline=PASS tests="<<TESTS<<" mode="<<mode<<" seed="<<argv[2]<<std::endl;
 auto start=std::chrono::steady_clock::now();uint64_t iter=0,restarts=0;int global=TESTS+1;
 std::array<Net,64>pool{};int npool=0;
 while(true){
  ++restarts;Net gs=npool&&ri(3)?pool[ri(npool)]:seednet();auto w=base;int score=eval(gs,w);
  double temp=mode==1?0.015:(0.08+ri(600)/1000.0);
  for(int local=0;local<250000;++local){
   ++iter;Net old=gs;int k=GATES;
   int number=(mode==2&&ri(4)==0)?2+ri(3):1;
   for(int z=0;z<number;++z){int i=ri(GATES);k=std::min(k,i);int kind=ri(20);
    if(kind<8)gs[i].a=ri(INPUTS+i);else if(kind<16)gs[i].b=ri(INPUTS+i);else if(kind<19)gs[i].is_and=!gs[i].is_and;else gs[i]={ri(INPUTS+i),ri(INPUTS+i),bool(ri(2))};
   }
   auto nw=w;int value=eval(gs,nw,k);
   if(value<=score||double(rnd()>>11)*0x1.0p-53<std::exp(double(score-value)/temp)){w=nw;score=value;}else gs=old;
   if(score<global){global=score;save(gs,argv[4],score,w);std::cout<<"best="<<score<<" iterations="<<iter<<" restarts="<<restarts<<std::endl;}
   if(score<=19&&local%2000==0){if(npool<64)pool[npool++]=gs;else pool[ri(64)]=gs;}
   if(score==0){std::cout<<"CANDIDATE all decisive tests passed; independent validation required"<<std::endl;return 0;}
   if((iter&65535)==0){auto elapsed=std::chrono::duration_cast<std::chrono::seconds>(std::chrono::steady_clock::now()-start).count();
    if(iter%1048576==0)std::cout<<"elapsed="<<elapsed<<" iterations="<<iter<<" best="<<global<<" current="<<score<<" restarts="<<restarts<<std::endl;
    if(elapsed>=seconds){std::cout<<"STOP time_budget elapsed="<<elapsed<<" iterations="<<iter<<" best="<<global<<" restarts="<<restarts<<std::endl;return 1;}
   }
  }
 }
}
