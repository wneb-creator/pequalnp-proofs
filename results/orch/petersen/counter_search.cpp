#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <random>
#include <vector>

// Finite computational exploration only; output is not a Lean certificate.
struct Gate { int a, b; bool is_and; };
constexpr int n = 10, k = 19;
std::vector<std::pair<int,int>> edges;
std::vector<int> max_independent;
using Circuit = std::array<Gate,k>;
std::array<uint64_t, n> inputs;
uint64_t target;
std::mt19937_64 rng(2583);
std::vector<int> samples;

uint64_t evaluate(const Circuit &c) {
  std::array<uint64_t,n+k> w;
  std::copy(inputs.begin(),inputs.end(),w.begin());
  for(int i=0;i<k;++i) w[n+i] = c[i].is_and ? w[c[i].a]&w[c[i].b] : w[c[i].a]|w[c[i].b];
  return w.back();
}
int score(const Circuit &c) { return __builtin_popcountll(evaluate(c)^target); }

Circuit seed() {
  std::vector<Gate> full;
  int independent=max_independent[rng()%max_independent.size()];
  std::array<std::vector<int>,n> assigned;
  for(auto [a,b]:edges) {
    if(independent&(1<<a)) assigned[b].push_back(a);
    else if(independent&(1<<b)) assigned[a].push_back(b);
    else if(rng()%2) assigned[a].push_back(b);
    else assigned[b].push_back(a);
  }
  std::vector<int> centers, roots;
  for(int i=0;i<n;++i) if(!assigned[i].empty()) centers.push_back(i);
  std::shuffle(centers.begin(),centers.end(),rng);
  for(int center:centers) {
    auto ps=assigned[center];
    std::shuffle(ps.begin(),ps.end(),rng);
    int root=ps[0];
    for(unsigned i=1;i<ps.size();++i) {
      full.push_back({root,ps[i],false}); root=n+(int)full.size()-1;
    }
    full.push_back({root,center,true}); roots.push_back(n+(int)full.size()-1);
  }
  while(roots.size()>1) {
    std::shuffle(roots.begin(),roots.end(),rng);
    int a=roots.back(); roots.pop_back(); int b=roots.back(); roots.pop_back();
    full.push_back({a,b,false}); roots.push_back(n+(int)full.size()-1);
  }
  if(full.size()!=20) std::abort();
  int del=rng()%20, replace=(rng()%2) ? full[del].a : full[del].b;
  auto reindex=[&](int x) {if(x==n+del) x=replace; if(x>n+del) --x; return x;};
  Circuit c; int j=0;
  for(int i=0;i<20;++i) if(i!=del) c[j++]={reindex(full[i].a),reindex(full[i].b),full[i].is_and};
  return c;
}

void print(const Circuit &c) {
  for(int i=0;i<k;++i) std::cout << i+n << ' ' << (c[i].is_and?"and":"or") << ' ' << c[i].a << ' ' << c[i].b << '\n';
}

int main(int argc,char **argv) {
  int seconds=argc>1?std::atoi(argv[1]):120;
  if(argc>2) rng.seed(std::strtoull(argv[2],nullptr,10));
  for(int i=0;i<5;++i) edges.push_back({i,(i+1)%5});
  for(int i=0;i<5;++i) edges.push_back({i,i+5});
  for(auto e:std::vector<std::pair<int,int>>{{5,7},{7,9},{9,6},{6,8},{8,5}}) edges.push_back(e);
  for(auto [a,b]:edges) samples.push_back((1<<a)|(1<<b));
  target=(1ULL<<samples.size())-1;
  auto accepts=[&](int mask) {for(auto [a,b]:edges) if((mask&(1<<a))&&(mask&(1<<b))) return true; return false;};
  for(int mask=0;mask<(1<<n);++mask) if(!accepts(mask)) {
    bool maximal=true;
    for(int i=0;i<n;++i) if(!(mask&(1<<i)) && !accepts(mask|(1<<i))) maximal=false;
    if(maximal) samples.push_back(mask);
    if(__builtin_popcount(mask)==4) max_independent.push_back(mask);
  }
  for(int i=0;i<n;++i) for(unsigned j=0;j<samples.size();++j) if(samples[j]&(1<<i)) inputs[i]|=1ULL<<j;
  std::cout << "samples " << samples.size() << " gates " << k << '\n';
  auto until=std::chrono::steady_clock::now()+std::chrono::seconds(seconds);
  uint64_t attempts=0,restarts=0; int best=99; Circuit bestc;
  while(std::chrono::steady_clock::now()<until) {
    Circuit c=seed(); int s=score(c); ++restarts;
    const double temperature=(restarts%4==0)?0.8:(restarts%4==1)?0.3:(restarts%4==2)?0.1:0.0;
    for(int iter=0;iter<100000;++iter) {
      ++attempts;
      int pos=rng()%k; Gate old=c[pos]; int mode=rng()%8;
      if(mode==0) c[pos].is_and=!c[pos].is_and;
      else if(mode<4) c[pos].a=rng()%(n+pos);
      else if(mode<7) c[pos].b=rng()%(n+pos);
      else {c[pos].a=rng()%(n+pos); c[pos].b=rng()%(n+pos); c[pos].is_and=rng()%2;}
      int t=score(c);
      if(t<=s || (temperature>0 && std::generate_canonical<double,53>(rng)<std::exp((s-t)/temperature))) s=t;
      else c[pos]=old;
      if(s<best) {
        best=s; bestc=c;
        std::cout << "best " << best << " attempts " << attempts << " restarts " << restarts << std::endl;
        if(best==0) {print(c); return 0;}
      }
      if((iter&8191)==0 && std::chrono::steady_clock::now()>=until) break;
    }
  }
  std::cout << "finished attempts " << attempts << " restarts " << restarts << " best " << best << '\n';
  print(bestc); return 1;
}
