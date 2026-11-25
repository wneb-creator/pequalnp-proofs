#include <algorithm>
#include <array>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <numeric>
#include <random>
#include <string>
#include <vector>

struct Gate { int op, a, b; };

int main(int argc, char **argv) {
  if (argc != 4) return 2;
  std::ifstream in(argv[1]);
  int n, k, m, upperk;
  uint64_t target;
  in >> n >> k >> m >> target >> upperk;
  std::vector<uint64_t> inputs(n);
  for (auto &x : inputs) in >> x;
  std::vector<Gate> upper(upperk);
  for (auto &g : upper) in >> g.op >> g.a >> g.b;
  if (!in || m > 64 || upperk != k+1) return 3;
  int seconds = std::stoi(argv[2]);
  uint64_t seed = std::stoull(argv[3]);
  std::mt19937_64 rng(seed);
  const uint64_t mask = m==64 ? ~0ULL : (1ULL<<m)-1;
  const auto start = std::chrono::steady_clock::now();
  auto elapsed = [&]() {return std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();};
  auto score = [&](const std::vector<Gate> &c) {
    std::array<uint64_t,128> wires{};
    for(int i=0;i<n;i++) wires[i]=inputs[i];
    for(int i=0;i<k;i++) wires[n+i]=c[i].op ? (wires[c[i].a]|wires[c[i].b]) : (wires[c[i].a]&wires[c[i].b]);
    return __builtin_popcountll((wires[n+k-1]^target)&mask);
  };
  auto print = [&](const std::vector<Gate>& c,int s,uint64_t iter,uint64_t restarts) {
    std::cout << "{\"score\":" << s << ",\"seconds\":" << elapsed() << ",\"iterations\":" << iter << ",\"restarts\":" << restarts << ",\"gates\":[";
    for(int i=0;i<k;i++){if(i)std::cout<<',';std::cout<<'['<<c[i].op<<','<<c[i].a<<','<<c[i].b<<']';}
    std::cout << "]}" << std::endl;
  };
  uint64_t total=0,restarts=0;
  int best=1000;
  std::vector<Gate> bestc;
  while(elapsed()<seconds) {
    restarts++;
    std::vector<int> done(upperk,0),mapping(n+upperk,-1);
    for(int i=0;i<n;i++)mapping[i]=i;
    std::vector<Gate> shuffled;
    for(int i=0;i<upperk;i++){
      std::vector<int> ready;
      for(int j=0;j<upperk;j++) if(!done[j]&&mapping[upper[j].a]>=0&&mapping[upper[j].b]>=0)ready.push_back(j);
      int j=ready[rng()%ready.size()];
      Gate g{upper[j].op,mapping[upper[j].a],mapping[upper[j].b]};
      if(g.a>g.b)std::swap(g.a,g.b);
      shuffled.push_back(g);done[j]=1;mapping[n+j]=n+i;
    }
    int drop=rng()%upperk;
    int substitute=(rng()&1)?shuffled[drop].a:shuffled[drop].b;
    std::vector<Gate> c;
    auto rewrite=[&](int w){if(w==n+drop)w=substitute;return w>n+drop?w-1:w;};
    for(int i=0;i<upperk;i++)if(i!=drop){Gate g=shuffled[i];g.a=rewrite(g.a);g.b=rewrite(g.b);if(g.a>g.b)std::swap(g.a,g.b);c.push_back(g);}
    int s=score(c);
    std::array<double,65> probs{};
    for(int iter=0;iter<50000;iter++){
      if((iter&1023)==0){
        if(elapsed()>=seconds){print(bestc,best,total,restarts);return 0;}
        double t=.05+1.2*(1.-double(iter)/50000.);
        for(int d=1;d<=64;d++)probs[d]=std::exp(-double(d)/t);
      }
      int j=rng()%k;Gate old=c[j];Gate g=old;
      switch(rng()%8){
        case 0:g.op^=1;break;
        case 1:case 2:case 3:g.a=rng()%(n+j);break;
        case 4:case 5:case 6:g.b=rng()%(n+j);break;
        default:g.op=rng()%2;g.a=rng()%(n+j);g.b=rng()%(n+j);break;
      }
      if(g.a>g.b)std::swap(g.a,g.b);
      if(g.a==g.b)continue;
      c[j]=g;int ns=score(c);total++;
      if(ns<=s||double(rng())/double(UINT64_MAX)<probs[ns-s])s=ns;else c[j]=old;
      if(s<best){best=s;bestc=c;print(c,s,total,restarts);if(!s)return 10;}
    }
  }
  print(bestc,best,total,restarts);
  return 0;
}
