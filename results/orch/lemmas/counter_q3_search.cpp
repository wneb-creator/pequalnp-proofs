#include <algorithm>
#include <array>
#include <bitset>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <random>
#include <vector>

// Finite computational exploration only; output is not a Lean certificate.
struct Gate { int a, b; bool is_and; };
constexpr int q = 3, N = q*q+q+1, n = 2*N, k = N*(q+2)-2;
using Mask = std::bitset<768>;
using Circuit = std::array<Gate,k>;
std::array<Mask, n> inputs;
Mask target;
std::mt19937_64 rng(2583);
std::vector<int> samples;

Mask evaluate(const Circuit &c) {
  std::array<Mask,n+k> w;
  std::copy(inputs.begin(),inputs.end(),w.begin());
  for(int i=0;i<k;++i) w[n+i] = c[i].is_and ? w[c[i].a]&w[c[i].b] : w[c[i].a]|w[c[i].b];
  return w.back();
}
int score(const Circuit &c) { return (evaluate(c)^target).count(); }

Circuit seed() {
  std::vector<Gate> full;
  std::array<int,N> stars;
  std::array<int,N> ls;
  for(int i=0;i<N;++i) ls[i]=i;
  std::shuffle(ls.begin(),ls.end(),rng);
  for(int l:ls) {
    std::array<int,4> ps = {l,(l+1)%N,(l+3)%N,(l+9)%N};
    std::shuffle(ps.begin(),ps.end(),rng);
    int root=ps[0];
    for(int i=1;i<4;++i) {
      full.push_back({root,ps[i],false});
      root=n+(int)full.size()-1;
    }
    full.push_back({root,N+l,true});
    stars[l] = n+(int)full.size()-1;
  }
  std::vector<int> roots(stars.begin(),stars.end());
  while(roots.size()>1) {
    std::shuffle(roots.begin(),roots.end(),rng);
    int a=roots.back(); roots.pop_back(); int b=roots.back(); roots.pop_back();
    full.push_back({a,b,false}); roots.push_back(n+(int)full.size()-1);
  }
  int del = rng()%(k+1), replace=(rng()%2) ? full[del].a : full[del].b;
  auto reindex=[&](int x) {if(x==n+del) x=replace; if(x>n+del) --x; return x;};
  Circuit c; int j=0;
  for(int i=0;i<k+1;++i) if(i!=del) c[j++]={reindex(full[i].a),reindex(full[i].b),full[i].is_and};
  return c;
}

void print(const Circuit &c) {
  for(int i=0;i<k;++i) std::cout << i+n << ' ' << (c[i].is_and?"and":"or") << ' ' << c[i].a << ' ' << c[i].b << '\n';
}

int main(int argc,char **argv) {
  int seconds=argc>1?std::atoi(argv[1]):120;
  if(argc>2) rng.seed(std::strtoull(argv[2],nullptr,10));
  for(int l=0;l<N;++l) for(int d:{0,1,3,9}) samples.push_back((1<<((l+d)%N))|(1<<(N+l)));
  for(unsigned j=0;j<samples.size();++j) target.set(j);
  for(int x=0;x<(1<<N);++x) {
    int y=0,covered=0;
    for(int l=0;l<N;++l) {
      int pts=(1<<l)|(1<<((l+1)%N))|(1<<((l+3)%N))|(1<<((l+9)%N));
      if(!(x&pts)) {y|=1<<l; covered|=pts;}
    }
    if((x|covered)==(1<<N)-1) samples.push_back(x|(y<<N));
  }
  if(samples.size()>768) return 2;
  for(int i=0;i<n;++i) for(unsigned j=0;j<samples.size();++j) if(samples[j]&(1<<i)) inputs[i].set(j);
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
