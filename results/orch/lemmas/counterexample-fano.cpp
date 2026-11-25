#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <random>
#include <vector>

struct Gate { int a,b; bool is_or; };
using Net=std::array<Gate,26>;
std::mt19937_64 rng(4675);
std::vector<std::pair<int,int>> edges;
std::vector<unsigned> cases;
uint64_t inputs[14]{},target;
uint64_t iterations=0;

int score(const Net& net) {
  uint64_t values[40]; unsigned colors[40];
  for(int i=0;i<14;++i) {values[i]=inputs[i];colors[i]=i<7?1:2;}
  int invalid=0;
  for(int j=0;j<26;++j) {
    auto g=net[j];
    if(g.is_or) {
      values[14+j]=values[g.a]|values[g.b]; colors[14+j]=colors[g.a]|colors[g.b];
      invalid+=colors[14+j]==3;
    } else {values[14+j]=values[g.a]&values[g.b]; colors[14+j]=0;}
  }
  return __builtin_popcountll(values[39]^target)+16*invalid;
}

Net seed() {
  bool flip=rng()%2;
  std::array<int,7> order; std::iota(order.begin(),order.end(),0); std::shuffle(order.begin(),order.end(),rng);
  std::vector<Gate> full;
  std::vector<int> outputs;
  for(int v:order) {
    int centre=v+(flip?7:0); std::vector<int> leaves;
    for(auto [a,b]:edges) if(centre==a) leaves.push_back(b); else if(centre==b) leaves.push_back(a);
    std::shuffle(leaves.begin(),leaves.end(),rng);
    int w=14+full.size(); full.push_back({leaves[0],leaves[1],true});
    full.push_back({w,leaves[2],true}); full.push_back({centre,w+1,false}); outputs.push_back(w+2);
  }
  while(outputs.size()>1) {
    std::shuffle(outputs.begin(),outputs.end(),rng);
    int a=outputs.back();outputs.pop_back();int b=outputs.back();outputs.pop_back();
    outputs.push_back(14+full.size());full.push_back({a,b,true});
  }
  int remove=3*(rng()%7)+(rng()%2);int replace=(rng()%2)?full[remove].a:full[remove].b;
  Net net; int k=0;
  auto remap=[&](int w) {if(w==14+remove) w=replace; return w>14+remove?w-1:w;};
  for(int j=0;j<27;++j) if(j!=remove) net[k++]={remap(full[j].a),remap(full[j].b),full[j].is_or};
  return net;
}

void printnet(const Net& net) {
  std::cout<<"WITNESS 26 gates, output39, p7 l7\n";
  for(auto [a,b]:edges) std::cout<<"EDGE "<<a<<' '<<b-7<<'\n';
  for(auto g:net) std::cout<<(g.is_or?"OR ":"AND ")<<g.a<<' '<<g.b<<'\n';
  std::cout.flush();
}

int main(int argc,char**argv) {
  int seconds=argc>1?std::atoi(argv[1]):60;
  int lines[7][3]={{0,1,2},{0,3,4},{0,5,6},{1,3,5},{1,4,6},{2,3,6},{2,4,5}};
  for(int b=0;b<7;++b) for(int a:lines[b]) edges.emplace_back(a,7+b);
  for(auto [a,b]:edges) cases.push_back((1u<<a)|(1u<<b));
  for(unsigned s=0;s<(1u<<14);++s) {
    bool independent=true;
    for(auto [a,b]:edges) if((s&(1u<<a))&&(s&(1u<<b))) {independent=false;break;}
    if(!independent) continue;
    bool maximal=true;
    for(int v=0;v<14;++v) if(!(s&(1u<<v))) {
      bool neighbor=false;
      for(auto [a,b]:edges) if((a==v&&(s&(1u<<b)))||(b==v&&(s&(1u<<a)))) neighbor=true;
      if(!neighbor) {maximal=false;break;}
    }
    if(maximal) cases.push_back(s);
  }
  if(cases.size()!=58) return 2;
  for(int i=0;i<14;++i) for(unsigned k=0;k<cases.size();++k) if(cases[k]&(1u<<i)) inputs[i]|=uint64_t(1)<<k;
  target=(uint64_t(1)<<21)-1;
  auto start=std::chrono::steady_clock::now();
  int global=10000;uint64_t restarts=0;
  while(std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<seconds) {
    Net current=seed();int best=score(current);++restarts;
    for(int local=0;local<100000;++local) {
      Net cand=current;
      int changes=1+(rng()%16==0?1:0)+(rng()%64==0?2:0);
      for(int k=0;k<changes;++k) {
        int j=rng()%26;int kind=rng()%3;
        if(kind==0) cand[j].is_or=!cand[j].is_or;
        else if(kind==1) cand[j].a=rng()%(14+j);
        else cand[j].b=rng()%(14+j);
      }
      int value=score(cand);++iterations;
      if(value<global) {global=value;std::cout<<"best="<<global<<" iterations="<<iterations<<" restarts="<<restarts<<std::endl;}
      if(value==0) {printnet(cand);return 1;}
      if(value<=best) {current=cand;best=value;}
      else if((rng()%100000)==0 && value<=best+2) {current=cand;best=value;}
    }
  }
  std::cout<<"NO WITNESS iterations="<<iterations<<" restarts="<<restarts<<" best="<<global<<std::endl;
}
