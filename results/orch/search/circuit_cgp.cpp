#include <algorithm>
#include <array>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <numeric>
#include <random>
#include <vector>
struct Gate { int op,a,b; };
struct Instance {int n,k,m,upperk;uint64_t target;std::vector<uint64_t> inputs;std::vector<Gate> upper;};
Instance load(const char *path){
  std::ifstream in(path);Instance z;in>>z.n>>z.k>>z.m>>z.target>>z.upperk;
  z.inputs.resize(z.n);for(auto &v:z.inputs)in>>v;
  z.upper.resize(z.upperk);for(auto &g:z.upper)in>>g.op>>g.a>>g.b;
  if(!in||z.m>64||z.n>32)throw 1;return z;
}
int main(int argc,char **argv){
  if(argc!=7){std::cerr<<"usage: circuit_cgp honest.input dirty.input seconds seed capacity control-only\n";return 2;}
  Instance a=load(argv[1]),b=load(argv[2]);
  if(a.n!=b.n||a.m!=b.m||a.target!=b.target||a.inputs!=b.inputs)return 3;
  int n=a.n,cap=std::stoi(argv[5]);if(cap<29||cap>60)return 4;
  int seconds=std::stoi(argv[3]);bool controls=std::stoi(argv[6]);
  std::mt19937_64 rng(std::stoull(argv[4]));
  auto start=std::chrono::steady_clock::now();
  auto elapsed=[&](){return std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();};
  auto truth=[&](const std::vector<Gate>& c,int output){
    std::array<uint64_t,128>w{};for(int i=0;i<n;i++)w[i]=a.inputs[i];
    for(int j=0;j<cap;j++)w[n+j]=c[j].op?(w[c[j].a]|w[c[j].b]):(w[c[j].a]&w[c[j].b]);
    return w[output];
  };
  auto reachable=[&](const std::vector<Gate>& c,int output){
    uint64_t bits=0;if(output<n)return bits;bits|=1ULL<<(output-n);
    for(int j=cap-1;j>=0;j--)if(bits>>j&1){if(c[j].a>=n)bits|=1ULL<<(c[j].a-n);if(c[j].b>=n)bits|=1ULL<<(c[j].b-n);}
    return bits;
  };
  auto fresh=[&](const Instance& z){
    std::vector<Gate> c(cap),topo;
    std::vector<int> done(z.upperk),ren(n+z.upperk,-1);for(int i=0;i<n;i++)ren[i]=i;
    for(int j=0;j<z.upperk;j++){
      std::vector<int> ready;for(int h=0;h<z.upperk;h++)if(!done[h]&&ren[z.upper[h].a]>=0&&ren[z.upper[h].b]>=0)ready.push_back(h);
      int h=ready[rng()%ready.size()];topo.push_back({z.upper[h].op,ren[z.upper[h].a],ren[z.upper[h].b]});done[h]=1;ren[n+h]=n+j;
    }
    std::vector<int> positions(cap-1);std::iota(positions.begin(),positions.end(),0);std::shuffle(positions.begin(),positions.end(),rng);positions.resize(z.upperk-1);positions.push_back(cap-1);std::sort(positions.begin(),positions.end());
    std::vector<int> map(n+z.upperk);for(int i=0;i<n;i++)map[i]=i;for(int j=0;j<z.upperk;j++)map[n+j]=n+positions[j];
    for(int j=0;j<cap;j++)c[j]={int(rng()&1),int(rng()%(n+j)),int(rng()%(n+j))};
    for(int j=0;j<z.upperk;j++)c[positions[j]]={topo[j].op,map[topo[j].a],map[topo[j].b]};
    return c;
  };
  auto print=[&](const std::vector<Gate>& c,int output,const char *kind,uint64_t iterations,uint64_t restarts){
    uint64_t bits=reachable(c,output);std::array<int,128>map{};for(int i=0;i<n;i++)map[i]=i;int count=0;
    std::cout<<"{\"kind\":\""<<kind<<"\",\"seconds\":"<<elapsed()<<",\"active_gates\":"<<__builtin_popcountll(bits)<<",\"total_gates\":"<<cap<<",\"iterations\":"<<iterations<<",\"restarts\":"<<restarts<<",\"score\":0,\"gates\":[";
    for(int j=0;j<cap;j++)if(bits>>j&1){if(count)std::cout<<',';std::cout<<'['<<c[j].op<<','<<map[c[j].a]<<','<<map[c[j].b]<<']';map[n+j]=n+count++;}
    std::cout<<"],\"output\":"<<map[output]<<'}'<<std::endl;
  };
  for(const auto *z:{&a,&b}){auto c=fresh(*z);if(truth(c,n+cap-1)!=a.target||__builtin_popcountll(reachable(c,n+cap-1))!=z->upperk)return 5;print(c,n+cap-1,z==&a?"control_honest":"control_dirty",0,0);}
  if(controls)return 0;
  int best=1000;uint64_t total=0,restarts=0;std::vector<Gate>bestc;int bestout=0;
  while(elapsed()<seconds){
    restarts++;auto c=fresh((rng()&1)?a:b);int output=n+cap-1;int size=__builtin_popcountll(reachable(c,output));
    for(int iter=0;iter<2000000;iter++){
      if((iter&8191)==0&&elapsed()>=seconds){print(bestc,bestout,"final",total,restarts);return 0;}
      total++;bool output_change=rng()%64==0;int oldout=output,j=rng()%cap;Gate old=c[j],g=old;
      if(output_change)output=rng()%(n+cap);
      else{
        switch(rng()%8){case 0:g.op^=1;break;case 1:case 2:case 3:g.a=rng()%(n+j);break;case 4:case 5:case 6:g.b=rng()%(n+j);break;default:g.op=rng()%2;g.a=rng()%(n+j);g.b=rng()%(n+j);break;}
        c[j]=g;
      }
      if(truth(c,output)!=a.target){c[j]=old;output=oldout;continue;}
      int ns=__builtin_popcountll(reachable(c,output));double t=.1+2.*(1.-double(iter)/2000000.);
      if(ns<=size||double(rng())/double(UINT64_MAX)<std::exp(double(size-ns)/t))size=ns;else{c[j]=old;output=oldout;}
      if(size<best){best=size;bestc=c;bestout=output;print(c,output,"improvement",total,restarts);if(size<=26)return 10;}
    }
  }
  print(bestc,bestout,"final",total,restarts);return 0;
}
