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

// Heuristic finite truth-table synthesis. A failure to find a witness is not a lower bound.
using Table = std::array<uint64_t,16>;
struct Gate { int op,a,b; };
struct Circuit { std::array<Gate,19> gates; };
std::mt19937_64 rng(2592096);
bool require_live_not=false;
std::array<Table,10> vars;
Table target, heavy;
const std::array<std::pair<int,int>,15> edges = {{{0,1},{1,2},{2,3},{3,4},{4,0},{0,5},{1,6},{2,7},{3,8},{4,9},{5,7},{7,9},{9,6},{6,8},{8,5}}};
int rnd(int n) { return rng()%n; }
int eval(const Circuit &c, int &plain) {
  std::array<Table,29> wires;
  std::array<unsigned,29> ancestors{};
  for(int i=0;i<10;i++) wires[i]=vars[i];
  int nots=0;unsigned notmask=0;
  for(int i=0;i<19;i++) {
    const auto g=c.gates[i]; nots+=g.op==2;
    if(g.op==2)notmask|=1u<<i;
    ancestors[10+i]=ancestors[g.a]|(g.op==2?0:ancestors[g.b])|(1u<<i);
    for(int j=0;j<16;j++) wires[10+i][j]=g.op==0 ? (wires[g.a][j]&wires[g.b][j]) : g.op==1 ? (wires[g.a][j]|wires[g.b][j]) : ~wires[g.a][j];
  }
  int score=0; plain=0;
  for(int j=0;j<16;j++) {
    const uint64_t delta=wires[28][j]^target[j];
    plain+=std::popcount(delta);
    score+=std::popcount(delta)+7*std::popcount(delta&heavy[j]);
  }
  if(require_live_not)return score+4*(19-std::popcount(ancestors[28]))+((notmask&ancestors[28])==0?100000:0);
  return score+(nots==0 ? 100000 : 0);
}
std::vector<Gate> star_circuit() {
  std::vector<int> valid;
  for(int s=0;s<1024;s++) {
    if(std::popcount((unsigned)s)!=6) continue;
    bool ok=true; for(auto [a,b]:edges) if(!(s>>a&1)&&!(s>>b&1)) ok=false;
    if(ok) valid.push_back(s);
  }
  int cover=valid[rnd(valid.size())];
  std::array<std::vector<int>,10> assigned;
  for(auto [a,b]:edges) {
    if(!(cover>>a&1)||((cover>>b&1)&&rnd(2))) std::swap(a,b);
    assigned[a].push_back(b);
  }
  std::vector<int> order;for(int v=0;v<10;v++)if(!assigned[v].empty())order.push_back(v);
  std::shuffle(order.begin(),order.end(),rng);
  std::vector<Gate> gs;std::vector<int> outputs;
  for(int v:order) {
    auto ns=assigned[v];std::shuffle(ns.begin(),ns.end(),rng);
    int x=ns[0];
    for(int k=1;k<(int)ns.size();k++){gs.push_back({1,x,ns[k]});x=9+gs.size();}
    gs.push_back({0,v,x});outputs.push_back(9+gs.size());
  }
  std::shuffle(outputs.begin(),outputs.end(),rng);
  int out=outputs[0];for(int k=1;k<(int)outputs.size();k++){gs.push_back({1,out,outputs[k]});out=9+gs.size();}
  return gs;
}
Circuit seed() {
  auto gs=star_circuit();
  while(gs.size()>19) {
    int k=rnd(gs.size()-1),replace=rnd(10+k);
    gs.erase(gs.begin()+k);
    for(auto &g:gs) for(int *p:{&g.a,&g.b})if(*p==10+k)*p=replace;else if(*p>10+k)--*p;
  }
  Circuit c;
  for(int i=0;i<19;i++)c.gates[i]=gs[i];
  int neg=rnd(18);c.gates[neg]={2,rnd(10+neg),0};
  return c;
}
void dump(const Circuit &c,int score,int plain,const std::string &path) {
  std::ofstream f(path);f<<"score "<<score<<" mismatches "<<plain<<"\n";
  for(int i=0;i<19;i++)f<<i+10<<" "<<c.gates[i].op<<" "<<c.gates[i].a<<" "<<c.gates[i].b<<"\n";
  f<<"output 28\n";
}
int main(int argc,char**argv) {
  int seconds=argc>1?std::stoi(argv[1]):300;
  std::string path=argc>2?argv[2]:"counterexample-best.txt";
  if(argc>3) rng.seed(std::stoull(argv[3]));
  if(argc>4)require_live_not=std::stoi(argv[4])!=0;
  for(int s=0;s<1024;s++) {
    bool t=false;for(auto [a,b]:edges)t=t||((s>>a&1)&&(s>>b&1));
    if(t)target[s/64]|=uint64_t(1)<<(s%64);
    if(!t||std::popcount((unsigned)s)==2)heavy[s/64]|=uint64_t(1)<<(s%64);
    for(int v=0;v<10;v++)if(s>>v&1)vars[v][s/64]|=uint64_t(1)<<(s%64);
  }
  auto start=std::chrono::steady_clock::now();
  long long trials=0;int best=100000, bestplain=0;Circuit champ;
  for(int restart=0;;restart++) {
    if(std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()>seconds)break;
    Circuit c=(best<100&&rnd(3)==0)?champ:seed();int plain,score=eval(c,plain);
    double temp0=1.0+3.0*(double(rnd(1000))/1000.0);
    for(int t=0;t<200000;t++) {
      Circuit d=c;int nmut=rnd(100)<4?2:1;
      for(int k=0;k<nmut;k++) {
        int i=rnd(19),part=rnd(3);
        if(part==0)d.gates[i].op=rnd(3);
        else if(part==1)d.gates[i].a=rnd(10+i);
        else d.gates[i].b=rnd(10+i);
      }
      int dp,ds=eval(d,dp);trials++;
      if(dp==0&&std::any_of(d.gates.begin(),d.gates.end(),[](Gate g){return g.op==2;})) {
        dump(d,ds,dp,path);std::cout<<"WITNESS trials "<<trials<<"\n";return 0;
      }
      double temp=temp0*(1.0-double(t)/200000.0)+0.02;
      if(ds<=score||double(rnd(1000000))/1000000.0<std::exp((score-ds)/temp)){c=d;score=ds;plain=dp;}
      if(score<best){best=score;bestplain=plain;champ=c;dump(c,best,bestplain,path);std::cout<<"best "<<best<<" mismatches "<<plain<<" trials "<<trials<<"\n"<<std::flush;}
      if(best==0){std::cout<<"WITNESS\n";return 0;}
      if(t%10000==0&&std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()>seconds)break;
    }
  }
  std::cout<<"DONE best "<<best<<" mismatches "<<bestplain<<" trials "<<trials<<"\n";
}
