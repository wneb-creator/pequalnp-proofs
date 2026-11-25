#include <algorithm>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <unordered_set>
#include <vector>

using U = std::uint64_t;

struct Search {
  int n, graph, m, budget;
  U nm, pm;
  std::vector<int> neg, pos;
  std::vector<U> vars, base, first, maximal;
  std::uint64_t states = 0;

  bool independent(int s) {
    int j=0;
    for (int a=0;a<n;a++) for(int b=a+1;b<n;b++,j++)
      if ((graph>>j&1) && (s>>a&1) && (s>>b&1)) return false;
    return true;
  }

  static std::vector<U> closure(std::vector<U> values, U extra) {
    const auto old = values;
    for (U a: old) values.push_back(a|extra);
    std::sort(values.begin(),values.end());
    values.erase(std::unique(values.begin(),values.end()),values.end());
    return values;
  }

  static std::vector<U> ands(const std::vector<U>& sides) {
    std::vector<U> result;
    for (std::size_t i=0;i<sides.size();i++)
      for (std::size_t j=i;j<sides.size();j++) result.push_back(sides[i]&sides[j]);
    std::sort(result.begin(),result.end());
    result.erase(std::unique(result.begin(),result.end()),result.end());
    return result;
  }

  Search(int n_, int graph_, int budget_): n(n_),graph(graph_),budget(budget_) {
    for(int s=0;s<(1<<n);s++) {
      if(!independent(s)) continue;
      bool ismax=true;
      for(int v=0;v<n;v++) if(!(s>>v&1) && independent(s|(1<<v))) ismax=false;
      if(ismax) neg.push_back(s);
    }
    for(int s:neg) for(int v=0;v<n;v++) if(!(s>>v&1)) pos.push_back(s|(1<<v));
    std::sort(pos.begin(),pos.end());
    pos.erase(std::unique(pos.begin(),pos.end()),pos.end());
    m=neg.size(); nm=(U(1)<<m)-1; pm=(U(1)<<pos.size())-1;
    for(int v=0;v<n;v++) {
      U value=0;
      for(int i=0;i<m;i++) if(neg[i]>>v&1) value|=U(1)<<i;
      for(int i=0;i<(int)pos.size();i++) if(pos[i]>>v&1) value|=U(1)<<(m+i);
      vars.push_back(value);
    }
    base={0}; for(U v:vars) base=closure(base,v);
    first=ands(base);
    for(U u=0;u<=nm;u++) {
      U value=0;
      for(U v:vars) if((v&nm&~u)==0) value|=v>>m;
      maximal.push_back(value);
    }
  }

  bool finish(U a, U b, int previous) {
    states++;
    U ap=a>>m, bp=b>>m, an=a&nm,bn=b&nm;
    U need=pm;
    if(previous>0 && an==0) need&=~ap;
    if(previous>1 && bn==0) need&=~bp;
    if(need==0) return true;
    // Every OR side can be enlarged to all signals whose negative footprint is
    // contained in a chosen u. A safe AND has disjoint side footprints, so
    // enlarging them to complementary masks u and nm^u preserves safety.
    for(U u=0;u<=(nm>>1);u++) {
      U w=nm^u;
      U p=maximal[u],q=maximal[w];
      if(previous>0) {if((an&~u)==0) p|=ap; if((an&~w)==0) q|=ap;}
      if(previous>1) {if((bn&~u)==0) p|=bp; if((bn&~w)==0) q|=bp;}
      if((p&need)==need && (q&need)==need) return true;
    }
    return false;
  }

  bool run() {
    if(budget==0) return pm==0;
    if(budget==1) return finish(0,0,0);
    for(U a:first) {
      if(budget==2) {if(finish(a,0,1)) return true; continue;}
      auto second=ands(closure(base,a));
      for(U b:second) if(finish(a,b,2)) return true;
    }
    return false;
  }
};

int main() {
  int n,g,k;
  while(std::cin>>n>>g>>k) {
    auto t=std::chrono::steady_clock::now();
    Search s(n,g,k);
    bool answer=s.run();
    double secs=std::chrono::duration<double>(std::chrono::steady_clock::now()-t).count();
    std::cout<<n<<" "<<g<<" "<<k<<" "<<(answer?"SAT":"UNSAT")
      <<" negative="<<s.neg.size()<<" positive="<<s.pos.size()
      <<" first="<<s.first.size()<<" states="<<s.states<<" seconds="<<secs<<std::endl;
  }
}
