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
using Net=std::vector<Gate>;
int gate_count=26, or_cap=100;
int negative_weight=100, activity_weight=0;
std::mt19937_64 rng(4675);
std::vector<std::pair<int,int>> edges;
std::vector<unsigned> cases;
uint64_t inputs[14]{},target;
uint64_t iterations=0;

struct Quality { int positive,negative,mixed,ors,active; };
Quality quality(const Net& net) {
  uint64_t values[100]; unsigned colors[100]; bool active[100]{};
  active[14+gate_count-1]=true;
  for(int j=gate_count-1;j>=0;--j) if(active[14+j]) {active[net[j].a]=true;active[net[j].b]=true;}
  for(int i=0;i<14;++i) {values[i]=inputs[i];colors[i]=i<7?1:2;}
  int invalid=0,ors=0,activity=0;
  for(int j=0;j<gate_count;++j) {
    auto g=net[j];
    if(g.is_or) {
      values[14+j]=values[g.a]|values[g.b]; colors[14+j]=colors[g.a]|colors[g.b];
      if(active[14+j]) {invalid+=colors[14+j]==3;++ors;}
    } else {values[14+j]=values[g.a]&values[g.b]; colors[14+j]=0;}
    activity+=active[14+j];
  }
  return {__builtin_popcountll(target&~values[14+gate_count-1]),
    __builtin_popcountll(values[14+gate_count-1]&~target),invalid,ors,activity};
}
int score(const Quality& q) {
  return q.positive*100+q.negative*negative_weight+q.mixed*300+
    std::max(0,q.ors-or_cap)*300+q.active*activity_weight;
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
  Net net(26); int k=0;
  auto remap=[&](int w) {if(w==14+remove) w=replace; return w>14+remove?w-1:w;};
  for(int j=0;j<27;++j) if(j!=remove) net[k++]={remap(full[j].a),remap(full[j].b),full[j].is_or};
  while(int(net.size())<gate_count) {
    int where=rng()%(net.size()+1);
    int source=where==int(net.size())?14+where-1:rng()%(14+where);
    for(auto& g:net) {if(g.a>=14+where)++g.a;if(g.b>=14+where)++g.b;}
    net.insert(net.begin()+where,{source,source,false});
  }
  return net;
}

void printnet(const Net& net) {
  std::cout<<"WITNESS raw_gates="<<gate_count<<" output="<<14+gate_count-1<<" p7 l7; remove inactive gates before certification\n";
  for(auto [a,b]:edges) std::cout<<"EDGE "<<a<<' '<<b-7<<'\n';
  for(auto g:net) std::cout<<(g.is_or?"OR ":"AND ")<<g.a<<' '<<g.b<<'\n';
  std::cout.flush();
}

int main(int argc,char**argv) {
  int seconds=argc>1?std::atoi(argv[1]):60;
  gate_count=argc>2?std::atoi(argv[2]):26;or_cap=argc>3?std::atoi(argv[3]):100;
  if(gate_count<26||gate_count>70) return 2;
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
    int weights[6]={10,25,50,100,200,400};
    negative_weight=weights[rng()%6];activity_weight=(rng()%4==0)?1:0;
    Net current=seed();int best=score(quality(current));++restarts;
    if(restarts%100==0) std::cout<<"restarts="<<restarts<<" iterations="<<iterations<<" best_exact_errors="<<global<<std::endl;
    for(int local=0;local<100000;++local) {
      Net cand=current;
      int changes=1+(rng()%8==0?1:0)+(rng()%32==0?2:0);
      for(int k=0;k<changes;++k) {
        int j=rng()%gate_count;int kind=rng()%3;
        if(kind==0) cand[j].is_or=!cand[j].is_or;
        else if(kind==1) cand[j].a=rng()%(14+j);
        else cand[j].b=rng()%(14+j);
      }
      Quality q=quality(cand);int value=score(q);++iterations;
      int exact=q.positive+q.negative+q.mixed*100+std::max(0,q.ors-or_cap)*100;
      if(exact<global) {global=exact;std::cout<<"best_exact_errors="<<global<<" positive="<<q.positive<<" negative="<<q.negative<<" mixed="<<q.mixed<<" active_OR="<<q.ors<<" active_gates="<<q.active<<" iterations="<<iterations<<" restarts="<<restarts<<std::endl;}
      if(exact==0) {printnet(cand);return 1;}
      if(value<=best) {current=cand;best=value;}
      else if((rng()%1000)==0 && value<=best+200) {current=cand;best=value;}
    }
  }
  std::cout<<"NO WITNESS iterations="<<iterations<<" restarts="<<restarts<<" best="<<global<<std::endl;
}
