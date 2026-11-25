#include "cadical.hpp"
#include <array>
#include <chrono>
#include <cstdlib>
#include <iostream>
#include <fstream>
#include <vector>
#include <algorithm>
#include <functional>
#include <string>

// Incremental finite-truth-table synthesis; witness search, not a formal proof.
// Sources 0..9 are inputs, 10 is false, 11+g is gate g.
struct Gate { int op, a, b; };
static const std::array<std::pair<int,int>,15> edges = {{
  {0,1},{1,2},{2,3},{3,4},{4,0},{0,5},{1,6},{2,7},{3,8},{4,9},
  {5,7},{7,9},{9,6},{6,8},{8,5}
}};
bool target(int x) {
  for(auto [a,b] : edges) if ((x & (1<<a)) && (x & (1<<b))) return true;
  return false;
}
struct Synthesis {
  CaDiCaL::Solver sat;
  int count, nv=0, zero, positiveMask=-1;
  std::vector<std::array<std::vector<int>,2>> selectors;
  std::vector<std::array<int,3>> ops;
  std::array<bool,1024> included{};
  int newvar() { return ++nv; }
  void onehot(const std::vector<int>& vs) {
    sat.clause(vs);
    for(size_t i=0;i<vs.size();++i) for(size_t j=0;j<i;++j)
      sat.clause(-vs[i],-vs[j]);
  }
  explicit Synthesis(int n, int seed):count(n),selectors(n),ops(n) {
    sat.set("quiet",1); sat.set("seed",seed);
    zero=newvar(); sat.clause(-zero);
    std::vector<int> someNot;
    for(int g=0;g<count;++g) {
      for(int k=0;k<3;++k) ops[g][k]=newvar();
      onehot(std::vector<int>(ops[g].begin(),ops[g].end()));
      someNot.push_back(ops[g][2]);
      for(int p=0;p<2;++p) {
        for(int s=0;s<11+g;++s) selectors[g][p].push_back(newvar());
        onehot(selectors[g][p]);
      }
      // Commuting binary operands may be ordered. Unary operands equalized.
      for(int a=0;a<11+g;++a) for(int b=0;b<11+g;++b) {
        if(a>b) sat.clause(-selectors[g][0][a],-selectors[g][1][b]);
        if(a!=b) sat.clause(-ops[g][2],-selectors[g][0][a],-selectors[g][1][b]);
      }
    }
    sat.clause(someNot);
  }
  void addrow(int x) {
    if(included[x]) return;
    included[x]=true;
    std::vector<int> values;
    for(int i=0;i<10;++i) values.push_back((x&(1<<i))?-zero:zero);
    values.push_back(zero);
    for(int g=0;g<count;++g) {
      int a=newvar(),b=newvar(),c=newvar();
      if(positiveMask>=0 && x==3) sat.clause(-ops[g][2],-a);
      if(positiveMask>=0 && x==positiveMask) sat.clause(-ops[g][2],a);
      int av[2]={a,b};
      for(int p=0;p<2;++p) for(int s=0;s<11+g;++s) {
        int sel=selectors[g][p][s], v=values[s], u=av[p];
        sat.clause(-sel,-u,v); sat.clause(-sel,u,-v);
      }
      // AND, OR, NOT, with three one-hot operation selectors.
      sat.clause(-ops[g][0],-c,a);
      sat.clause(-ops[g][0],-c,b);
      sat.clause(-ops[g][0],c,-a,-b);
      sat.clause(-ops[g][1],c,-a);
      sat.clause(-ops[g][1],c,-b);
      sat.clause(-ops[g][1],-c,a,b);
      sat.clause(-ops[g][2],c,a);
      sat.clause(-ops[g][2],-c,-a);
      values.push_back(c);
    }
    sat.clause(target(x)?values.back():-values.back());
  }
  std::vector<Gate> model() {
    std::vector<Gate> gs;
    for(int g=0;g<count;++g) {
      Gate v{-1,-1,-1};
      for(int o=0;o<3;++o) if(sat.val(ops[g][o])>0) v.op=o;
      for(int s=0;s<11+g;++s) {
        if(sat.val(selectors[g][0][s])>0) v.a=s;
        if(sat.val(selectors[g][1][s])>0) v.b=s;
      }
      gs.push_back(v);
    }
    return gs;
  }
};
bool evaluate(const std::vector<Gate>& gs, int x) {
  bool v[64];
  for(int i=0;i<10;++i)v[i]=(x&(1<<i)); v[10]=false;
  for(size_t g=0;g<gs.size();++g) {
    auto [op,a,b]=gs[g];
    v[11+g]=op==0?(v[a]&&v[b]):op==1?(v[a]||v[b]):!v[a];
  }
  return v[10+gs.size()];
}
int main(int argc,char**argv) {
  int n=argc>1?std::atoi(argv[1]):19;
  int duration=argc>2?std::atoi(argv[2]):1800;
  int seed=argc>3?std::atoi(argv[3]):104;
  Synthesis s(n,seed);
  if(argc>4) {
    std::ifstream pins(argv[4]);
    for(int g=0;g<n;++g) {
      int op,a,b; if(!(pins>>op>>a>>b)) break;
      if(a>b)std::swap(a,b);
      s.sat.clause(s.ops[g][op]);
      s.sat.clause(s.selectors[g][0][a]);
      s.sat.clause(s.selectors[g][1][b]);
    }
  }
  if(argc>5 && std::string(argv[5])=="sorted") {
    // Optional additional search restriction: nondecreasing last source.
    for(int g=0;g+1<n;++g)
      for(int a=0;a<11+g;++a) for(int b=0;b<a;++b)
        s.sat.clause(-s.selectors[g][1][a],-s.selectors[g+1][1][b]);
  }
  if(argc>6) {
    int k=std::atoi(argv[6]);
    std::vector<int> selected;
    std::function<void(int,int,int)> subsets = [&](int start,int remaining,int sign) {
      if(!remaining) {s.sat.clause(selected);return;}
      for(int i=start;i<=n-remaining;++i) {
        selected.push_back(sign*s.ops[i][2]);
        subsets(i+1,remaining-1,sign); selected.pop_back();
      }
    };
    subsets(0,k+1,-1); subsets(0,n-k+1,1);
  }
  bool minimal=argc>7 && std::string(argv[7])=="minimal";
  if(argc>8) s.positiveMask=std::atoi(argv[8]);
  for(int x=0;x<1024;++x) {
    bool maximalNegative=!target(x);
    if(maximalNegative) for(int i=0;i<10;++i)
      if(!(x&(1<<i))&&!target(x|(1<<i)))maximalNegative=false;
    if((minimal?(maximalNegative||(__builtin_popcount((unsigned)x)==2&&target(x))||x==0):
       (!target(x)||__builtin_popcount((unsigned)x)<=2))||x==1023) s.addrow(x);
  }
  auto begin=std::chrono::steady_clock::now();
  int rounds=0;
  while(true) {
    int elapsed=std::chrono::duration_cast<std::chrono::seconds>(std::chrono::steady_clock::now()-begin).count();
    if(elapsed>duration) {std::cout<<"TIME LIMIT, inconclusive\n"<<std::flush;return 0;}
    std::cout<<"round "<<rounds++<<" elapsed "<<elapsed<<" vars "<<s.nv<<" rows "
      <<std::count(s.included.begin(),s.included.end(),true)<<"\n"<<std::flush;
    s.sat.limit("conflicts",100000);
    int result=s.sat.solve();
    if(result==0) {std::cout<<"conflict budget, continuing\n"<<std::flush; continue;}
    if(result==20) {std::cout<<"UNSAT for encoded circuit class and tested rows\n"<<std::flush;return 20;}
    auto gs=s.model(); std::vector<int> bad;
    for(int x=0;x<1024;++x) if(evaluate(gs,x)!=target(x))bad.push_back(x);
    std::cout<<"candidate mismatches "<<bad.size()<<"\n"<<std::flush;
    if(bad.empty()) {
      std::cout<<"WITNESS gates="<<n<<"\n";
      for(auto [op,a,b]:gs)std::cout<<op<<" "<<a<<" "<<b<<"\n";
      std::cout<<std::flush;return 10;
    }
    for(int x:bad)s.addrow(x);
  }
}
