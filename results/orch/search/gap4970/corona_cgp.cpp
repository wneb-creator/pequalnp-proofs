#include <algorithm>
#include <array>
#include <cassert>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <random>
#include <stdexcept>
#include <string>
#include <vector>

// Adapted from the earlier circuit_cgp.cpp. A retained circuit includes a
// semantic witness for every edge, even when the witness is not an ancestor
// of the output. All 4096 assignments are evaluated exactly.
constexpr int N = 12, P = 6, M = 12, WORDS = 64, MAXG = 60;
const std::array<int,6> core = {0,6,1,7,2,8};
const std::array<int,6> leaves = {9,3,10,4,11,5};
using Truth = std::array<uint64_t, WORDS>;
struct Gate { int op, a, b; };
struct Circuit { std::vector<Gate> gates; int output; };
struct Eval {
  bool correct = false, valid = false;
  uint64_t keep = 0;
  int size = 1000;
  std::vector<int> witnesses;
};
std::array<Truth, N> inputs;
Truth target;
std::vector<std::pair<int,int>> edges;
std::array<unsigned, 1 << N> starCover{};
std::array<Truth, 1 << N> starTruth{};

void initialize() {
  for (int i=0; i<6; ++i) {
    for (int w : {core[(i+1)%6], leaves[i]}) {
      int a=core[i], b=w;
      if (a>=P) std::swap(a,b);
      edges.emplace_back(a,b);
    }
  }
  for (int x=0; x<(1<<N); ++x) {
    for (int i=0; i<N; ++i) if (x>>i&1) inputs[i][x/64] |= 1ULL<<(x%64);
    for (auto [a,b]:edges) if ((x>>a&1) && (x>>b&1)) {
      target[x/64] |= 1ULL<<(x%64); break;
    }
  }
  for (int centre=0; centre<N; ++centre) {
    unsigned neighbors=0;
    for (auto [a,b]:edges) {
      if (a==centre) neighbors|=1U<<b;
      if (b==centre) neighbors|=1U<<a;
    }
    for (unsigned q=neighbors; q; q=(q-1)&neighbors) if (__builtin_popcount(q)>=2) {
      unsigned covered=0;
      for (unsigned i=0; i<edges.size(); ++i) {
        auto [a,b]=edges[i];
        if ((a==centre && (q>>b&1)) || (b==centre && (q>>a&1))) covered|=1U<<i;
      }
      starCover[q]|=covered;
      for (int i=0; i<N; ++i) if (q>>i&1)
        for (int k=0; k<WORDS; ++k) starTruth[q][k]|=inputs[i][k];
    }
  }
}

Eval evaluate(const Circuit &c) {
  Eval result;
  int k=c.gates.size();
  if (k>MAXG || c.output<0 || c.output>=N+k) return result;
  std::array<Truth,N+MAXG> truth{};
  std::array<unsigned,N+MAXG> reach{};
  std::array<uint64_t,N+MAXG> ancestors{};
  std::array<unsigned,MAXG> covers{};
  for (int i=0; i<N; ++i) { truth[i]=inputs[i]; reach[i]=1U<<i; }
  uint64_t mixed=0;
  unsigned allCover=0;
  for (int j=0; j<k; ++j) {
    auto [op,a,b]=c.gates[j];
    if (op<0 || op>1 || a<0 || b<0 || a>=N+j || b>=N+j) return result;
    ancestors[N+j]=ancestors[a]|ancestors[b]|(1ULL<<j);
    for (int z=0; z<WORDS; ++z)
      truth[N+j][z]=op ? (truth[a][z]|truth[b][z]) : (truth[a][z]&truth[b][z]);
    if (op) {
      reach[N+j]=reach[a]|reach[b];
      if ((reach[N+j]&((1U<<P)-1)) && (reach[N+j]&(((1U<<N)-1)^((1U<<P)-1))))
        mixed|=1ULL<<j;
      unsigned support=0;
      for (int i=0; i<N; ++i) {
        int one=1<<i;
        if (truth[N+j][one/64]>>(one%64)&1) support|=1U<<i;
      }
      if (starCover[support] && truth[N+j]==starTruth[support] &&
          !(ancestors[N+j]&mixed)) {
        covers[j]=starCover[support]; allCover|=covers[j];
      }
    }
  }
  if (truth[c.output]!=target) return result;
  result.correct=true;
  uint64_t initial=ancestors[c.output];
  if ((initial&mixed) || allCover!=((1U<<M)-1)) return result;
  // Greedy selection is an upper bound on the joint cone cost, not an exact
  // minimization. Every retained candidate is independently revalidated.
  uint64_t keep=initial;
  unsigned covered=0;
  for (int j=0; j<k; ++j) if (keep>>j&1) covered|=covers[j];
  std::vector<int> witnesses;
  while (covered!=((1U<<M)-1)) {
    int choice=-1, bestCost=1000, bestGain=0;
    for (int j=0; j<k; ++j) {
      int gain=__builtin_popcount(covers[j]&~covered);
      if (!gain) continue;
      int cost=__builtin_popcountll(ancestors[N+j]&~keep);
      if (choice<0 || cost*bestGain<bestCost*gain ||
          (cost*bestGain==bestCost*gain && (gain>bestGain || (gain==bestGain && j<choice)))) {
        choice=j;bestCost=cost;bestGain=gain;
      }
    }
    if (choice<0) return result;
    witnesses.push_back(choice); keep|=ancestors[N+choice];
    for (int j=0; j<k; ++j) if (keep>>j&1) covered|=covers[j];
  }
  assert(!(keep&mixed));
  result.valid=true;result.keep=keep;result.size=__builtin_popcountll(keep);
  for (int j=0; j<k; ++j) if ((keep>>j&1) && covers[j]) result.witnesses.push_back(j);
  return result;
}

Circuit compact(const Circuit &c, const Eval &e) {
  Circuit d;std::array<int,N+MAXG> map{};
  for (int i=0; i<N; ++i) map[i]=i;
  for (int j=0; j<(int)c.gates.size(); ++j) if (e.keep>>j&1) {
    auto g=c.gates[j]; map[N+j]=N+d.gates.size();
    d.gates.push_back({g.op,map[g.a],map[g.b]});
  }
  d.output=map[c.output];return d;
}

int add(Circuit &c, int op, int a, int b) {
  c.gates.push_back({op,a,b});return N+c.gates.size()-1;
}
int unite(Circuit &c, const std::vector<int> &w) {
  assert(!w.empty());int z=w[0];
  for (unsigned i=1; i<w.size(); ++i) z=add(c,1,z,w[i]);
  return z;
}
Circuit canonical() {
  Circuit c;std::vector<int> terms;
  for (int i=0; i<6; ++i) {
    int q=add(c,1,leaves[i],core[(i+1)%6]);
    terms.push_back(add(c,0,core[i],q));
  }
  c.output=unite(c,terms);return c;
}
Circuit deadWitnesses() {
  Circuit c;std::vector<int> terms;
  for(auto [a,b]:edges)terms.push_back(add(c,0,a,b));
  c.output=unite(c,terms);
  for(int i=0; i<6; ++i)add(c,1,leaves[i],core[(i+1)%6]);
  return c;
}

void print(const Circuit &c,const Eval &e,const char *kind,double seconds,
           uint64_t iterations,uint64_t restarts) {
  Circuit d=compact(c,e);Eval check=evaluate(d);
  if (!check.valid || (int)d.gates.size()!=e.size) throw std::runtime_error("invalid emitted circuit");
  std::cout<<"{\"kind\":\""<<kind<<"\",\"graph\":\"c6_corona\",\"seconds\":"<<seconds
           <<",\"iterations\":"<<iterations<<",\"restarts\":"<<restarts
           <<",\"gate_count\":"<<d.gates.size()<<",\"and_count\":"
           <<std::count_if(d.gates.begin(),d.gates.end(),[](Gate g){return !g.op;})
           <<",\"t_count\":0,\"edges_served\":12,\"truth_rows\":4096,\"gates\":[";
  for(unsigned j=0;j<d.gates.size();++j) {
    if(j)std::cout<<',';auto g=d.gates[j];std::cout<<'['<<g.op<<','<<g.a<<','<<g.b<<']';
  }
  std::cout<<"],\"output\":"<<d.output<<",\"witness_gate_indices\":[";
  for(unsigned j=0;j<check.witnesses.size();++j){if(j)std::cout<<',';std::cout<<check.witnesses[j];}
  std::cout<<"]}"<<std::endl;
}

int main(int argc,char **argv) {
  if(argc!=5) {
    std::cerr<<"usage: gap4970_corona_cgp seconds seed capacity control-only\n";return 2;
  }
  int seconds=std::stoi(argv[1]),cap=std::stoi(argv[3]);
  bool controls=std::stoi(argv[4]);
  if(seconds<0 || cap<17 || cap>MAXG)return 2;
  initialize();std::mt19937_64 rng(std::stoull(argv[2]));
  auto start=std::chrono::steady_clock::now();
  auto elapsed=[&](){return std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();};
  Circuit seed=canonical();Eval se=evaluate(seed);
  if(!se.valid || se.size!=17)return 3;
  print(seed,se,"control_canonical",elapsed(),0,0);
  Circuit dead=deadWitnesses();Eval de=evaluate(dead);
  if(!de.valid || de.size!=29 || dead.output==N+(int)dead.gates.size()-1)return 4;
  print(dead,de,"control_postoutput_witnesses",elapsed(),0,0);
  Circuit missing=dead;missing.gates.resize(23);
  if(!evaluate(missing).correct || evaluate(missing).valid)return 5;
  Circuit wrong=seed;wrong.gates.back().op=0;
  if(evaluate(wrong).correct)return 6;
  Circuit mixed=seed;
  std::vector<int> ins(N);std::iota(ins.begin(),ins.end(),0);
  int all=unite(mixed,ins);mixed.output=add(mixed,0,mixed.output,all);
  if(!evaluate(mixed).correct || evaluate(mixed).valid)return 7;
  // The final guard is semantically mixed, but every line enters it through
  // an AND barrier. All guard OR-only reaches therefore contain points only.
  // The guard is true whenever the graph function is true.
  Circuit shielded=seed;std::vector<int> guardInputs;
  for(int i=0;i<P;++i)guardInputs.push_back(i);
  for(int i=P;i<N;++i)guardInputs.push_back(add(shielded,0,i,i));
  int guard=unite(shielded,guardInputs);
  shielded.output=add(shielded,0,shielded.output,guard);
  Eval sh=evaluate(shielded);
  if(!sh.valid || sh.size!=35)return 8;
  print(shielded,sh,"control_duplicate_and_shields",elapsed(),0,0);
  if(controls)return 0;
  auto fresh=[&](){
    Circuit c;c.gates.resize(cap);
    std::vector<int> positions(cap);std::iota(positions.begin(),positions.end(),0);
    std::shuffle(positions.begin(),positions.end(),rng);positions.resize(seed.gates.size());
    std::sort(positions.begin(),positions.end());
    std::array<int,N+MAXG> map{};for(int i=0;i<N;++i)map[i]=i;
    for(unsigned j=0;j<positions.size();++j)map[N+j]=N+positions[j];
    for(int j=0;j<cap;++j)c.gates[j]={int(rng()&1),int(rng()%(N+j)),int(rng()%(N+j))};
    for(unsigned j=0;j<positions.size();++j){auto g=seed.gates[j];c.gates[positions[j]]={g.op,map[g.a],map[g.b]};}
    c.output=map[seed.output];return c;
  };
  Circuit best=seed;Eval be=se;
  uint64_t iterations=0,restarts=0,accepted=0;
  while(elapsed()<seconds) {
    ++restarts;Circuit c=fresh();Eval ce=evaluate(c);
    if(!ce.valid)throw std::runtime_error("invalid seed embedding");
    for(int step=0;step<250000;++step) {
      if((step&1023)==0 && elapsed()>=seconds)break;
      ++iterations;int output=c.output,j=rng()%cap;Gate old=c.gates[j];
      if(rng()%40==0)c.output=rng()%(N+cap);
      else {
        switch(rng()%8) {
          case 0:c.gates[j].op^=1;break;
          case 1:case 2:case 3:c.gates[j].a=rng()%(N+j);break;
          case 4:case 5:case 6:c.gates[j].b=rng()%(N+j);break;
          default:c.gates[j]={int(rng()&1),int(rng()%(N+j)),int(rng()%(N+j))};break;
        }
      }
      Eval ne=evaluate(c);
      double temp=0.10+1.5*(1.-double(step)/250000.);
      bool take=ne.valid && (ne.size<=ce.size ||
        double(rng())/double(UINT64_MAX)<std::exp(double(ce.size-ne.size)/temp));
      if(take){ce=ne;++accepted;}else{c.gates[j]=old;c.output=output;}
      if(ce.size<be.size) {
        best=c;be=ce;print(best,be,"improvement",elapsed(),iterations,restarts);
        if(be.size<=16)return 10;
      }
    }
  }
  print(best,be,"final_no_counterexample",elapsed(),iterations,restarts);
  std::cerr<<"accepted_mutations="<<accepted<<" iterations="<<iterations<<" restarts="<<restarts<<'\n';
  return 0;
}
