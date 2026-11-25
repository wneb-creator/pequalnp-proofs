#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <random>
#include <vector>

struct Gate { int a,b; bool is_and; };
using Net=std::array<Gate,26>;
uint64_t rng_state;
uint64_t rnd(){rng_state^=rng_state<<13;rng_state^=rng_state>>7;return rng_state^=rng_state<<17;}
int ri(int n){return rnd()%n;}
std::array<uint64_t,40> base;
uint64_t target=(uint64_t(1)<<21)-1;
std::vector<int> constraints;

Net seednet(){
  std::vector<Gate> gs;
  std::vector<int> outs;
  std::array<int,7> order{0,1,2,3,4,5,6};
  for(int i=6;i>0;--i)std::swap(order[i],order[ri(i+1)]);
  for(int l:order){
    std::array<int,3> p{l,(l+1)%7,(l+3)%7};
    for(int i=2;i>0;--i)std::swap(p[i],p[ri(i+1)]);
    int n=14+gs.size();
    gs.push_back({p[0],p[1],false});
    gs.push_back({n,p[2],false});
    gs.push_back({n+1,7+l,true});
    outs.push_back(n+2);
  }
  while(outs.size()>1){
    int i=ri(outs.size());int a=outs[i];outs.erase(outs.begin()+i);
    i=ri(outs.size());int b=outs[i];outs.erase(outs.begin()+i);
    outs.push_back(14+gs.size());gs.push_back({a,b,false});
  }
  int rem=ri(26), repl=ri(2)?gs[rem].a:gs[rem].b;
  Net out; int j=0;
  auto rw=[&](int w){if(w==14+rem)w=repl;return w>14+rem?w-1:w;};
  for(int i=0;i<27;++i)if(i!=rem)out[j++]={rw(gs[i].a),rw(gs[i].b),gs[i].is_and};
  return out;
}
int eval(const Net& gs,std::array<uint64_t,40>& w,int from=0){
  for(int j=from;j<26;++j)w[14+j]=gs[j].is_and?(w[gs[j].a]&w[gs[j].b]):(w[gs[j].a]|w[gs[j].b]);
  return std::popcount(w[39]^target);
}
void save(const Net& gs,const char* path,int score){
 std::ofstream f(path);f<<"score "<<score<<"\n";
 for(auto g:gs)f<<(g.is_and?"and":"or")<<" "<<g.a<<" "<<g.b<<"\n";
}
bool fullcheck(const Net& gs){
 for(int m=0;m<(1<<14);++m){
  std::array<bool,40>w{};for(int i=0;i<14;++i)w[i]=(m>>i)&1;
  for(int j=0;j<26;++j)w[14+j]=gs[j].is_and?(w[gs[j].a]&&w[gs[j].b]):(w[gs[j].a]||w[gs[j].b]);
  bool f=false;for(int l=0;l<7;++l)for(int p:{l,(l+1)%7,(l+3)%7})f|=w[p]&&w[7+l];
  if(w[39]!=f)return false;
 }
 return true;
}
int main(int argc,char**argv){
 if(argc!=5)return 2;
 int seconds=std::stoi(argv[1]);rng_state=std::stoull(argv[2]);
 std::ifstream f(argv[3]);int m;while(f>>m)constraints.push_back(m);
 if(constraints.size()!=58)return 3;
 for(int i=0;i<14;++i)for(int j=0;j<58;++j)if(constraints[j]>>i&1)base[i]|=uint64_t(1)<<j;
 auto start=std::chrono::steady_clock::now();
 uint64_t iter=0,restarts=0;int global=100;
 std::array<Net,32> pool;int npool=0;
 while(true){
  ++restarts;Net gs=npool&&ri(2)?pool[ri(npool)]:seednet();auto w=base;int score=eval(gs,w);
  double temp=ri(5)?0.02:(0.05+ri(1000)/5000.0);
  for(int local=0;local<50000;++local){
    ++iter;int k=ri(26);Gate old=gs[k];
    int kind=ri(20);
    if(kind<8)gs[k].a=ri(14+k);
    else if(kind<16)gs[k].b=ri(14+k);
    else if(kind<19)gs[k].is_and=!gs[k].is_and;
    else {gs[k]={ri(14+k),ri(14+k),bool(ri(2))};}
    auto nw=w;int s=eval(gs,nw,k);
    double accept=std::exp(double(score-s)/temp);
    if(s<=score || double(rnd()>>11)*0x1.0p-53<accept){w=nw;score=s;}
    else gs[k]=old;
    if(score<global){global=score;save(gs,argv[4],score);std::cout<<"best="<<score<<" iterations="<<iter<<" restarts="<<restarts<<std::endl;}
    if(score==1 && local%1000==0){pool[ri(32)]=gs;if(npool<32)pool[npool++]=gs;}
    if(score==0){std::cout<<"full_truth_table="<<(fullcheck(gs)?"PASS":"FAIL")<<std::endl;return fullcheck(gs)?0:4;}
    if(iter%10000000==0){
     int elapsed=std::chrono::duration_cast<std::chrono::seconds>(std::chrono::steady_clock::now()-start).count();
     std::cout<<"elapsed="<<elapsed<<" iterations="<<iter<<" best="<<global<<" current="<<score<<" restarts="<<restarts<<std::endl;
     if(elapsed>=seconds)return 1;
    }
  }
 }
}
