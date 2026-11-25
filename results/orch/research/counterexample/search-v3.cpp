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
  for(int rep=0;rep<2000;rep++) {
    std::vector<Gate> raw;
    auto add=[&](int op,int a,int b) { raw.push_back({op,a,b}); return inputs+(int)raw.size()-1; };
    auto disj=[&](std::vector<int> terms) {
      while(terms.size()>1) {
        std::shuffle(terms.begin(),terms.end(),rng);
        int a=terms.back(); terms.pop_back(); int b=terms.back(); terms.pop_back();
        terms.push_back(add(0,a,b));
      }
      return terms[0];
    };
    int common=rnd(7);
    std::vector<int> centres{common,(common+1)%7,(common+3)%7};
    std::shuffle(centres.begin(),centres.end(),rng);
    if(rnd(2)) centres.pop_back();
    int outer=disj(centres);
    std::vector<int> inner{7+common};
    for(int p:centres) {
      std::vector<int> others;
      for(int l=0;l<7;l++) if(l!=common && ((p-l+7)%7==0 || (p-l+7)%7==1 || (p-l+7)%7==3)) others.push_back(7+l);
      inner.push_back(add(1,p,disj(others)));
    }
    std::vector<int> roots{add(1,outer,disj(inner))};
    std::vector<int> remaining;
    for(int p=0;p<7;p++) if(std::find(centres.begin(),centres.end(),p)==centres.end()) remaining.push_back(p);
    std::shuffle(remaining.begin(),remaining.end(),rng);
    for(int p:remaining) {
      std::vector<int> neighbours;
      for(int l=0;l<7;l++) if((p-l+7)%7==0 || (p-l+7)%7==1 || (p-l+7)%7==3) neighbours.push_back(7+l);
      roots.push_back(add(1,p,disj(neighbours)));
    }
    int output=disj(roots);
    if(rnd(2)) for(auto& g:raw) {
      auto dual=[](int w) { return w<7 ? 7+(7-w)%7 : w<14 ? (14-w)%7 : w; };
      g.a=dual(g.a); g.b=dual(g.b);
    }
    if(raw.size()!=28 || output!=41) return 5;
    std::array<U,42> check;
    std::copy(columns.begin(),columns.end(),check.begin());
    for(int j=0;j<28;j++) { auto g=raw[j]; check[inputs+j]=g.op ? check[g.a]&check[g.b] : check[g.a]|check[g.b]; }
    if(check[output]!=target) { std::cerr<<"incorrect nonlinear seed\n"; return 6; }
    if(rep==0) {
      std::ofstream out("/tmp/oec/pequalnp-pilot-137/counterexample/nonlinear-28-seed.txt");
      out<<"output "<<output<<'\n';
      for(int j=0;j<28;j++) out<<inputs+j<<' '<<(raw[j].op ? "AND" : "OR")<<' '<<raw[j].a<<' '<<raw[j].b<<'\n';
    }
    int deleted=rnd(27), replacement=rnd(2) ? raw[deleted].a : raw[deleted].b;
    auto relabel=[&](int w) { if(w==inputs+deleted) return replacement; return w>inputs+deleted ? w-1 : w; };
    std::array<Gate,27> init;
    for(int j=0,k=0;j<28;j++) if(j!=deleted) { auto g=raw[j]; init[k++]={g.op,relabel(g.a),relabel(g.b)}; }
    seeds.push_back(remove(init,rnd(27),rnd(2)));
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
