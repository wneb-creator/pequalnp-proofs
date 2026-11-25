#include <array>
#include <algorithm>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <random>
#include <vector>

using U = uint64_t;
constexpr int inputs = 14;
constexpr int gates = 26;
struct Gate { int op, a, b; };
struct Circ { std::array<Gate,gates> g; int output=inputs+gates-1; };
std::array<U,inputs> columns;
U target;
int patterns;
std::mt19937_64 rng(1372583);
int rnd(int n) { return rng()%n; }
int score(const Circ& c) {
  std::array<U,inputs+gates> values;
  std::copy(columns.begin(), columns.end(), values.begin());
  for (int k=0;k<gates;k++) {
    auto g=c.g[k];
    values[inputs+k]=g.op ? values[g.a]&values[g.b] : values[g.a]|values[g.b];
  }
  return __builtin_popcountll(values[c.output]^target);
}
void dump(const Circ& c, std::ostream& out) {
  out << "output " << c.output << '\n';
  for(int k=0;k<gates;k++) out << inputs+k << ' ' << (c.g[k].op ? "AND" : "OR") << ' ' << c.g[k].a << ' ' << c.g[k].b << '\n';
}
Circ remove(const std::array<Gate,gates+1>& init, int k, int side) {
  Circ c;
  int replace=side ? init[k].b : init[k].a;
  auto relabel=[&](int w) { if(w==inputs+k) return replace; return w>inputs+k ? w-1 : w; };
  for(int i=0,j=0;i<=gates;i++) if(i!=k) { auto g=init[i]; c.g[j++]={g.op,relabel(g.a),relabel(g.b)}; }
  c.output=relabel(inputs+gates);
  return c;
}
int main(int argc, char** argv) {
  if(argc!=4) { std::cerr << "usage: search problem.txt seconds seed\n"; return 2; }
  std::ifstream in(argv[1]);
  in>>patterns>>target;
  for(auto& x:columns) in>>x;
  std::array<Gate,gates+1> initial;
  for(auto& g:initial) in>>g.op>>g.a>>g.b;
  if(!in) return 3;
  double seconds=std::stod(argv[2]); rng.seed(std::stoull(argv[3]));
  std::vector<Circ> seeds;
  for(int k=0;k<=gates;k++) for(int side=0;side<2;side++) seeds.push_back(remove(initial,k,side));
  int best=100;
  Circ champion;
  auto start=std::chrono::steady_clock::now();
  uint64_t iterations=0,restarts=0;
  for (;;) {
    Circ current=seeds[rnd(seeds.size())];
    if (restarts%4!=0 && best<100) current=champion;
    int value=score(current);
    int rounds=200000;
    for(int step=0;step<rounds;step++) {
      if((iterations++ & 65535)==0) {
        double elapsed=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();
        if(elapsed>=seconds) { std::cout<<"Finished seconds="<<elapsed<<" iterations="<<iterations<<" restarts="<<restarts<<" best="<<best<<std::endl; dump(champion,std::cout); return 1; }
      }
      Circ next=current;
      int k=rnd(gates);
      int mode=rnd(100);
      if(mode<3) next.output=rnd(inputs+gates);
      else if(mode<15) next.g[k].op^=1;
      else if(mode<53) next.g[k].a=rnd(inputs+k);
      else if(mode<91) next.g[k].b=rnd(inputs+k);
      else { next.g[k]={rnd(2),rnd(inputs+k),rnd(inputs+k)}; }
      int nv=score(next);
      if(nv<best) {
        best=nv; champion=next;
        double elapsed=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();
        std::cout<<"BEST score="<<best<<" seconds="<<elapsed<<" iterations="<<iterations<<" restarts="<<restarts<<std::endl;
        dump(champion,std::cout); std::cout.flush();
        if(best==0) { std::cout<<"WITNESS\n"; return 0; }
      }
      double fraction=(double)step/rounds;
      double temperature=(restarts%3==0 ? 0.65 : restarts%3==1 ? 0.35 : 1.1)*(1.0-fraction)+0.03;
      if(nv<=value || std::generate_canonical<double,53>(rng)<std::exp((value-nv)/temperature)) { current=next; value=nv; }
    }
    restarts++;
  }
}
