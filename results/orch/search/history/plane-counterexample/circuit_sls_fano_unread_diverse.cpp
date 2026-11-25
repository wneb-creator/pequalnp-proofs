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
#include <set>
#include <vector>

struct Gate { int op, a, b; };

int main(int argc, char **argv) {
  if (argc != 8) return 2;
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
  const int positive_weight=std::stoi(argv[4]);
  const int ep=std::stoi(argv[5]), el=std::stoi(argv[6]), read_weight=std::stoi(argv[7]);
  std::mt19937_64 rng(seed);
  const uint64_t mask = m==64 ? ~0ULL : (1ULL<<m)-1;
  const auto start = std::chrono::steady_clock::now();
  auto elapsed = [&]() {return std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();};
  auto errors = [&](const std::vector<Gate> &c) {
    std::array<uint64_t,128> wires{};
    for(int i=0;i<n;i++) wires[i]=inputs[i];
    for(int i=0;i<k;i++) wires[n+i]=c[i].op ? (wires[c[i].a]|wires[c[i].b]) : (wires[c[i].a]&wires[c[i].b]);
    return (wires[n+k-1]^target)&mask;
  };
  auto has_read = [&](const std::vector<Gate> &c) {
    std::array<int,128> r{};r[ep]=1;r[el]=2;
    for(int i=0;i<k;i++){int a=r[c[i].a],b=r[c[i].b];r[n+i]=c[i].op?(a|b):(((a&1)&&(b&2))||((a&2)&&(b&1))?4:0);}
    return (r[n+k-1]&4)!=0;
  };
  auto score = [&](const std::vector<Gate> &c) { uint64_t e=errors(c); return positive_weight*__builtin_popcountll(e&target)+__builtin_popcountll(e&~target)+read_weight*has_read(c); };
  auto print = [&](const std::vector<Gate>& c,int s,uint64_t iter,uint64_t restarts) {
    uint64_t e=errors(c);
    std::cout << "{\"fixed_edge_read1\":" << (has_read(c)?"true":"false") << ",\"weighted_score\":" << s << ",\"positive_errors\":" << __builtin_popcountll(e&target) << ",\"negative_errors\":" << __builtin_popcountll(e&~target) << ",\"error_mask\":" << e << ",";
    std::cout << "\"score\":" << __builtin_popcountll(e) << ",\"seconds\":" << elapsed() << ",\"iterations\":" << iter << ",\"restarts\":" << restarts << ",\"gates\":[";
    for(int i=0;i<k;i++){if(i)std::cout<<',';std::cout<<'['<<c[i].op<<','<<c[i].a<<','<<c[i].b<<']';}
    std::cout << "]}" << std::endl;
  };
  if(n!=14 || upperk!=27) return 4;
  std::vector<std::vector<int>> neighbors(n);
  for(int bit=0;bit<m;bit++) if((target>>bit)&1){
    std::vector<int> vs;
    for(int i=0;i<n;i++)if((inputs[i]>>bit)&1)vs.push_back(i);
    if(vs.size()!=2)return 5;
    neighbors[vs[0]].push_back(vs[1]);neighbors[vs[1]].push_back(vs[0]);
  }
  auto fresh_upper=[&]() {
    std::vector<Gate> built;std::vector<int> terms;
    auto add=[&](int op,int a,int b){if(a>b)std::swap(a,b);built.push_back({op,a,b});return n+int(built.size())-1;};
    auto unite=[&](std::vector<int> active){
      while(active.size()>1){int ia=rng()%active.size();int a=active[ia];active.erase(active.begin()+ia);int ib=rng()%active.size();int b=active[ib];active.erase(active.begin()+ib);active.push_back(add(1,a,b));}
      return active[0];
    };
    if(rng()%3==0){
      int center=(rng()&1)?1:3;
      int lp=unite(neighbors[7]);int rp=unite(neighbors[center]);
      int rect=add(0,lp,rp);int filter=add(1,center,7);terms.push_back(add(0,rect,filter));
      for(int line=8;line<14;line++){
        std::vector<int> remaining;
        for(int point:neighbors[line])if(point!=center)remaining.push_back(point);
        int sum=unite(remaining);terms.push_back(add(0,line,sum));
      }
      unite(terms);
      if(rng()&1){auto dual=[](int w){return w>=14?w:w<7?7+(7-w)%7:(14-w)%7;};for(auto &g:built){g.a=dual(g.a);g.b=dual(g.b);}}
      return built;
    }
    int side=(rng()&1)?7:0;
    std::vector<int> centers(7);std::iota(centers.begin(),centers.end(),side);std::shuffle(centers.begin(),centers.end(),rng);
    for(int center:centers){int sum=unite(neighbors[center]);terms.push_back(add(0,center,sum));}
    unite(terms);return built;
  };
  uint64_t total=0,restarts=0;
  int best=1000;
  std::vector<Gate> bestc;
  std::set<uint64_t> near_masks;
  int best_over=1000;
  while(elapsed()<seconds) {
    restarts++;
    upper=fresh_upper();upperk=upper.size();
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
    while(int(shuffled.size())>k){
      int drop=rng()%shuffled.size();
      int substitute=(rng()&1)?shuffled[drop].a:shuffled[drop].b;
      auto rewrite=[&](int w){if(w==n+drop)w=substitute;return w>n+drop?w-1:w;};
      std::vector<Gate> smaller;
      for(int i=0;i<int(shuffled.size());i++)if(i!=drop){Gate g=shuffled[i];g.a=rewrite(g.a);g.b=rewrite(g.b);if(g.a>g.b)std::swap(g.a,g.b);smaller.push_back(g);}
      shuffled=std::move(smaller);
    }
    std::vector<Gate> c=std::move(shuffled);
    int s=score(c);
    std::vector<double> probs(64*positive_weight+read_weight+1);
    for(int iter=0;iter<50000;iter++){
      if((iter&1023)==0){
        if(elapsed()>=seconds){print(bestc,best,total,restarts);return 0;}
        double t=.05+1.2*(1.-double(iter)/50000.);
        for(int d=1;d<=64*positive_weight+read_weight;d++)probs[d]=std::exp(-double(d)/t);
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
      uint64_t e=errors(c);
      if(e==0){print(c,s,total,restarts);return 10;}
      if(s<best){best=s;bestc=c;print(c,s,total,restarts);if(!s)return 10;}
      if((e&target)==0 && !has_read(c) && s<=best_over){if(s<best_over){best_over=s;near_masks.clear();}if(near_masks.insert(e).second)print(c,s,total,restarts);}
    }
  }
  print(bestc,best,total,restarts);
  return 0;
}
