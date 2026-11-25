#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <numeric>
#include <random>
#include <vector>

using TT = std::array<uint64_t,16>;
struct Gate { int op,a,b; };
struct Circuit { std::vector<Gate> gs; int out; };
constexpr int B=12, N=19;
std::mt19937_64 rng;
int pick(int n) { return int(rng()%n); }
std::array<TT,B> base;
TT target;
std::vector<std::pair<int,int>> edges={{0,1},{1,2},{2,3},{3,4},{4,0},{0,5},{1,6},{2,7},{3,8},{4,9},{5,7},{7,9},{9,6},{6,8},{8,5}};
std::vector<int> covers;
std::vector<std::array<int,10>> automorphisms;
uint64_t evaluations=0;

std::pair<int,int> errors(const Circuit& c) {
  ++evaluations;
  std::array<TT,B+N> vals;
  std::copy(base.begin(),base.end(),vals.begin());
  for(int i=0;i<(int)c.gs.size();++i) {
    auto [op,a,b]=c.gs[i];
    for(int k=0;k<16;++k) vals[B+i][k]=op==0 ? vals[a][k]&vals[b][k] : op==1 ? vals[a][k]|vals[b][k] : ~vals[a][k];
  }
  int fp=0,fn=0;
  for(int k=0;k<16;++k) { fp+=std::popcount(vals[c.out][k]&~target[k]); fn+=std::popcount(~vals[c.out][k]&target[k]); }
  return {fp,fn};
}

void save(const Circuit& c,const std::string& name,int fp,int fn) {
  std::ofstream f(name);
  f << "{\"false_positives\":"<<fp<<",\"false_negatives\":"<<fn<<",\"output\":";
  auto wire=[](int w){return w<B ? (w>=10 ? 1000000 : w) : w-2;};
  f << wire(c.out) << ",\"gates\":[";
  for(size_t i=0;i<c.gs.size();++i) { auto [op,a,b]=c.gs[i]; if(i)f<<","; f<<"[\""<<(op==0?"and":op==1?"or":"not")<<"\","<<wire(a); if(op!=2)f<<","<<wire(b); f<<"]"; }
  f << "]}\n";
}

Circuit seed() {
  int mask=covers[pick(covers.size())];
  std::array<std::vector<int>,10> stars;
  for(auto [a,b]:edges) {
    if(!(mask>>a&1)) std::swap(a,b);
    else if((mask>>b&1)&&pick(2)) std::swap(a,b);
    stars[a].push_back(b);
  }
  Circuit c;
  auto gate=[&](int op,int a,int b){int j=B+c.gs.size();c.gs.push_back({op,a,b});return j;};
  std::vector<int> vertices(10),roots;
  std::iota(vertices.begin(),vertices.end(),0);
  std::shuffle(vertices.begin(),vertices.end(),rng);
  for(int a:vertices) if(stars[a].size()) {
    auto &ns=stars[a];std::shuffle(ns.begin(),ns.end(),rng);
    int j=ns[0]; for(size_t k=1;k<ns.size();++k)j=gate(1,j,ns[k]);
    roots.push_back(gate(0,a,j));
  }
  while(roots.size()>1) {
    std::shuffle(roots.begin(),roots.end(),rng);
    int a=roots.back();roots.pop_back();int b=roots.back();roots.pop_back();
    roots.push_back(gate(1,a,b));
  }
  c.out=roots[0];
  while(c.gs.size()>N) {
    int i=pick(c.gs.size()),w=B+i;
    int replacement=pick(2)?c.gs[i].a:c.gs[i].b;
    auto remap=[&](int z){return z==w ? replacement : z>w ? z-1:z;};
    c.gs.erase(c.gs.begin()+i);
    for(auto &g:c.gs) {g.a=remap(g.a);g.b=remap(g.b);}
    c.out=remap(c.out);
  }
  return c;
}

std::vector<int> active(const Circuit&c) {
  std::array<bool,B+N> used{};used[c.out]=true;
  for(int i=N-1;i>=0;--i)if(used[B+i]) {used[c.gs[i].a]=true;if(c.gs[i].op!=2)used[c.gs[i].b]=true;}
  std::vector<int> a;
  for(int i=0;i<N;++i)if(used[B+i])a.push_back(i);
  return a;
}

std::pair<int,bool> category(const Circuit&c) {
  std::array<TT,B+N> vals;std::copy(base.begin(),base.end(),vals.begin());
  std::array<bool,B+N> used{};used[c.out]=true;
  for(int i=N-1;i>=0;--i)if(used[B+i]){used[c.gs[i].a]=true;used[c.gs[i].b]=true;}
  int unsafe=0;
  for(int i=0;i<N;++i){
    auto[op,a,b]=c.gs[i];bool bad=false;
    for(int k=0;k<16;++k){vals[B+i][k]=op==0?vals[a][k]&vals[b][k]:vals[a][k]|vals[b][k];bad|=bool(vals[B+i][k]&~target[k]);}
    if(used[B+i]&&op==0&&bad)++unsafe;
  }
  return {unsafe,false};
}

Circuit approximateSeed() {
  std::vector<Gate> lean={{1,2,0},{1,3,9},{1,9,5},{1,6,5},{1,11,6},{0,1,15},
    {1,0,12},{1,3,14},{0,8,18},{0,15,18},{1,13,2},{0,7,21},{0,21,20},
    {1,4,23},{0,24,17},{1,22,16},{1,25,19},{1,26,27}};
  const auto &p=automorphisms[pick(automorphisms.size())];
  Circuit c;
  for(auto g:lean){auto map=[&](int w){return w<10?p[w]:w==10?10:w+1;};c.gs.push_back({g.op,map(g.a),map(g.b)});}
  c.gs.push_back({1,B+17,11});c.out=B+18;
  return c;
}

void mutate(Circuit&c,int count) {
  auto a=active(c);
  for(int m=0;m<count;++m) {
    if(pick(80)==0) {c.out=pick(B+N);continue;}
    int i=a.size()&&pick(5) ? a[pick(a.size())] : pick(N);
    auto &g=c.gs[i];
    int type=pick(9);
    if(type<1)g.op=pick(2);
    else if(type<5)g.a=pick(B+i);
    else g.b=pick(B+i);
  }
}

int main(int argc,char**argv) {
  int seconds=argc>1?std::stoi(argv[1]):900;
  uint64_t randomseed=argc>2?std::stoull(argv[2]):std::chrono::steady_clock::now().time_since_epoch().count();
  rng.seed(randomseed);
  for(int x=0;x<1024;++x) {
    for(int j=0;j<10;++j)if(x>>j&1)base[j][x/64]|=uint64_t(1)<<(x%64);
    
    for(auto [a,b]:edges)if((x>>a&1)&&(x>>b&1)){target[x/64]|=uint64_t(1)<<(x%64);break;}
  }
  for(int m=0;m<1024;++m)if(std::popcount((unsigned)m)==6) {
    bool ok=true;for(auto [a,b]:edges)if(!(m>>a&1)&&!(m>>b&1))ok=false;
    if(ok)covers.push_back(m);
  }
  bool adjacent[10][10]{};
  for(auto[a,b]:edges)adjacent[a][b]=adjacent[b][a]=true;
  std::array<int,10> perm;std::iota(perm.begin(),perm.end(),0);
  do {
    
    bool ok=true;for(auto[a,b]:edges)if(!adjacent[perm[a]][perm[b]]){ok=false;break;}
    if(ok)automorphisms.push_back(perm);
  }while(std::next_permutation(perm.begin(),perm.end()));
  int global=1025;uint64_t runs=0;
  auto begin=std::chrono::steady_clock::now(),last=begin;
  std::cout<<"seed "<<randomseed<<" covers "<<covers.size()<<" automorphisms "<<automorphisms.size()<<" seconds "<<seconds<<std::endl;
  std::array<std::vector<Circuit>,8> eliteGroups;
  std::array<int,8> eliteScores;eliteScores.fill(1025);
  while(std::chrono::duration<double>(std::chrono::steady_clock::now()-begin).count()<seconds) {
    ++runs;
    int group=2*pick(4),wantedNeg=group/2;bool wantedSeed=false;
    auto &elites=eliteGroups[group];
    Circuit c=elites.size()&&pick(3) ? elites[pick(elites.size())] : pick(2)?seed():approximateSeed();
    if(elites.size()&&pick(2))mutate(c,1+pick(8));
    auto [fp,fn]=errors(c);
    double weight=std::exp((pick(101)-50)/30.0);
    auto penalty=[&](const Circuit&z){auto[n,s]=category(z);return 3.0*std::abs(n-wantedNeg)+(s==wantedSeed?0:3);};
    double score=fp*weight+fn+penalty(c);
    int stagnant=0;
    for(int iter=0;iter<20000;++iter) {
      Circuit d=c;int count=1;
      while(count<8&&pick(6)==0)++count;
      mutate(d,count);
      auto [p,n]=errors(d);double s=p*weight+n+penalty(d);
      if(p+n<global) {
        global=p+n;
        std::cout<<"best "<<global<<" fp "<<p<<" fn "<<n<<" eval "<<evaluations<<" runs "<<runs<<" time "<<std::chrono::duration<double>(std::chrono::steady_clock::now()-begin).count()<<std::endl;
        save(d,"best.json",p,n);
        if(global==0) {save(d,"counterexample.json",p,n);return 0;}
      }
      auto [negs,usesSeed]=category(d);int dg=std::min(3,negs)*2+usesSeed;
      if(p+n<eliteScores[dg]) {
        eliteScores[dg]=p+n;eliteGroups[dg].clear();eliteGroups[dg].push_back(d);
        save(d,"best-category-"+std::to_string(dg)+".json",p,n);
        std::cout<<"category "<<dg<<" error "<<p+n<<" unsafe_ands "<<negs<<" unused_flag "<<usesSeed<<" eval "<<evaluations<<std::endl;
      } else if(p+n==eliteScores[dg]&&pick(10000)==0) {
        auto &es=eliteGroups[dg];if(es.size()<32)es.push_back(d);else es[pick(es.size())]=d;
      }
      double temp=0.3*(1.0-double(iter)/20000.0);
      if(s<score || (s==score&&pick(4)) || (temp>0&&pick(1000000)<1000000*std::exp((score-s)/temp))) {
        if(s<score)stagnant=0;else ++stagnant;
        c=std::move(d);score=s;fp=p;fn=n;
      } else ++stagnant;
      if(iter%1000==0&&std::chrono::duration<double>(std::chrono::steady_clock::now()-begin).count()>=seconds)break;
      if(stagnant>6000)break;
    }
    auto now=std::chrono::steady_clock::now();
    if(std::chrono::duration<double>(now-last).count()>30) {
      std::cout<<"progress best "<<global<<" eval "<<evaluations<<" runs "<<runs<<" elapsed "<<std::chrono::duration<double>(now-begin).count()<<std::endl;last=now;
    }
  }
  std::cout<<"DONE best "<<global<<" eval "<<evaluations<<" runs "<<runs<<std::endl;
  return 2;
}
