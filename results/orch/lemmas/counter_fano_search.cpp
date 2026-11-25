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
constexpr int n = 14, k = 26;
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
  std::array<int,7> stars;
  std::array<int,7> ls = {0,1,2,3,4,5,6};
  std::shuffle(ls.begin(),ls.end(),rng);
  for(int l:ls) {
    std::array<int,3> ps = {l,(l+1)%7,(l+3)%7};
    std::shuffle(ps.begin(),ps.end(),rng);
    full.push_back({ps[0],ps[1],false});
    full.push_back({n+(int)full.size()-1,ps[2],false});
    full.push_back({n+(int)full.size()-1,7+l,true});
    stars[l] = n+(int)full.size()-1;
  }
  std::vector<int> roots(stars.begin(),stars.end());
  while(roots.size()>1) {
    std::shuffle(roots.begin(),roots.end(),rng);
    int a=roots.back(); roots.pop_back(); int b=roots.back(); roots.pop_back();
    full.push_back({a,b,false}); roots.push_back(n+(int)full.size()-1);
  }
  int del = rng()%27, replace=(rng()%2) ? full[del].a : full[del].b;
  auto reindex=[&](int x) {if(x==n+del) x=replace; if(x>n+del) --x; return x;};
  Circuit c; int j=0;
  for(int i=0;i<27;++i) if(i!=del) c[j++]={reindex(full[i].a),reindex(full[i].b),full[i].is_and};
  return c;
}

void print(const Circuit &c) {
  for(int i=0;i<k;++i) std::cout << i+n << ' ' << (c[i].is_and?"and":"or") << ' ' << c[i].a << ' ' << c[i].b << '\n';
}

int main(int argc,char **argv) {
  int seconds=argc>1?std::atoi(argv[1]):120;
  if(argc>2) rng.seed(std::strtoull(argv[2],nullptr,10));
  for(int l=0;l<7;++l) for(int d:{0,1,3}) samples.push_back((1<<((l+d)%7))|(1<<(7+l)));
  target=(1ULL<<samples.size())-1;
  for(int x=0;x<128;++x) {
    int y=0;
    for(int l=0;l<7;++l) if(!(x&(1<<l))&&!(x&(1<<((l+1)%7)))&&!(x&(1<<((l+3)%7)))) y|=1<<l;
    bool maximal=true;
    for(int p=0;p<7;++p) if(!(x&(1<<p))) {
      bool hit=false;
      for(int l=0;l<7;++l) if(y&(1<<l)) if(p==l || p==(l+1)%7 || p==(l+3)%7) hit=true;
      if(!hit) maximal=false;
    }
    if(maximal) samples.push_back(x|(y<<7));
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
