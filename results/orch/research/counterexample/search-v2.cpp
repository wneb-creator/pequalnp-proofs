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
U errors(const Circ& c) {
  std::array<U,inputs+gates> values;
  std::copy(columns.begin(), columns.end(), values.begin());
  for (int k=0;k<gates;k++) {
    auto g=c.g[k];
    values[inputs+k]=g.op ? values[g.a]&values[g.b] : values[g.a]|values[g.b];
  }
  return values[c.output]^target;
}
int score(U err, int weight) { return weight*__builtin_popcountll(err&target)+__builtin_popcountll(err&~target); }
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
  for (int rep=0;rep<500;rep++) {
    std::array<Gate,gates+1> init;
    int count=0;
    std::vector<int> centres{0,1,2,3,4,5,6}, roots;
    std::shuffle(centres.begin(),centres.end(),rng);
    bool dual=rnd(2);
    for(int c:centres) {
      std::vector<int> adj;
      for(int a=0;a<7;a++) if(dual ? ((c-a+7)%7==0 || (c-a+7)%7==1 || (c-a+7)%7==3) : ((a-c+7)%7==0 || (a-c+7)%7==1 || (a-c+7)%7==3)) adj.push_back(dual ? a+7 : a);
      std::shuffle(adj.begin(),adj.end(),rng);
      init[count++]={0,adj[0],adj[1]};
      init[count]={0,inputs+count-1,adj[2]}; count++;
      init[count]={1,inputs+count-1,dual ? c : c+7}; count++;
      roots.push_back(inputs+count-1);
    }
    while(roots.size()>1) {
      std::shuffle(roots.begin(),roots.end(),rng);
      int a=roots.back(); roots.pop_back(); int b=roots.back(); roots.pop_back();
      init[count++]={0,a,b}; roots.push_back(inputs+count-1);
    }
    std::array<U,inputs+gates+1> check;
    std::copy(columns.begin(),columns.end(),check.begin());
    for(int j=0;j<=gates;j++) { auto g=init[j]; check[inputs+j]=g.op ? check[g.a]&check[g.b] : check[g.a]|check[g.b]; }
    if(check.back()!=target) { std::cerr<<"incorrect seed\n"; return 4; }
    for(int side=0;side<2;side++) seeds.push_back(remove(init,rnd(gates+1),side));
  }
  std::vector<Circ> pool=seeds;
  int best=100;
  Circ champion;
  auto start=std::chrono::steady_clock::now();
  uint64_t iterations=0,restarts=0;
  for (;;) {
    Circ current=restarts%4==0 ? seeds[rnd(seeds.size())] : pool[rnd(pool.size())];
    int weight=(restarts%4==0 ? 1 : restarts%4==1 ? 3 : restarts%4==2 ? 8 : 25);
    int value=score(errors(current),weight);
    int rounds=200000;
    for(int step=0;step<rounds;step++) {
      if((iterations++ & 65535)==0) {
        double elapsed=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();
        if(elapsed>=seconds) { std::cout<<"Finished seconds="<<elapsed<<" iterations="<<iterations<<" restarts="<<restarts<<" best="<<best<<std::endl; dump(champion,std::cout); return 1; }
      }
      Circ next=current;
      int k=rnd(gates);
      int mode=rnd(100);
      if(mode<2) next.output=rnd(inputs+gates);
      else if(mode<12) next.g[k].op^=1;
      else if(mode<50) next.g[k].a=rnd(inputs+k);
      else if(mode<88) next.g[k].b=rnd(inputs+k);
      else if(mode<95 && k+1<gates && next.g[k+1].a!=inputs+k && next.g[k+1].b!=inputs+k) {
        std::swap(next.g[k],next.g[k+1]);
        auto relabel=[&](int& w) { if(w==inputs+k) w++; else if(w==inputs+k+1) w--; };
        for(int j=k+2;j<gates;j++) { relabel(next.g[j].a); relabel(next.g[j].b); }
        relabel(next.output);
      }
      else { next.g[k]={rnd(2),rnd(inputs+k),rnd(inputs+k)}; }
      U err=errors(next);
      int nv=score(err,weight), total=__builtin_popcountll(err);
      if(total<best) {
        best=total; champion=next;
        double elapsed=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();
        std::cout<<"BEST score="<<best<<" seconds="<<elapsed<<" iterations="<<iterations<<" restarts="<<restarts<<std::endl;
        dump(champion,std::cout); std::cout.flush();
        if(best==0) { std::cout<<"WITNESS\n"; return 0; }
      }
      if(total<=2 && rnd(1000)==0) { if(pool.size()<5000) pool.push_back(next); else pool[rnd(pool.size())]=next; }
      double fraction=(double)step/rounds;
      double temperature=(restarts%3==0 ? 0.65 : restarts%3==1 ? 0.35 : 1.1)*(1.0-fraction)+0.03;
      if(nv<=value || std::generate_canonical<double,53>(rng)<std::exp((value-nv)/temperature)) { current=next; value=nv; }
    }
    restarts++;
  }
}
