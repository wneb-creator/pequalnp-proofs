#include <array>
#include <bit>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <random>
#include <vector>

constexpr int N = 19;
using Bits = std::array<uint64_t, 16>;
struct Gate { int op, a, b; };
using Circuit = std::array<Gate, N>;
const std::array<std::pair<int,int>,15> edges = {{{0,1},{1,2},{2,3},{3,4},{4,0},{0,5},{1,6},{2,7},{3,8},{4,9},{5,7},{7,9},{9,6},{6,8},{8,5}}};
std::array<Bits,10> inputs{};
Bits target{};
std::mt19937_64 rng;
bool requireNot=false;
bool requireUsedNot=false;

int score(const Circuit &c, int weight) {
  std::array<Bits,10+N> values{};
  for (int i=0;i<10;i++) values[i]=inputs[i];
  for (int i=0;i<N;i++) {
    const auto &g=c[i];
    for (int j=0;j<16;j++) values[10+i][j]=g.op==0 ? values[g.a][j]&values[g.b][j] : g.op==1 ? values[g.a][j]|values[g.b][j] : ~values[g.a][j];
  }
  int result=0;
  for (int j=0;j<16;j++) {
    result += std::popcount(values[10+N-1][j] & ~target[j])*weight;
    result += std::popcount(~values[10+N-1][j] & target[j]);
  }
  if(requireNot) {
    bool hasNot=false;
    std::array<bool,10+N> used{};
    used[10+N-1]=true;
    for(int i=N-1;i>=0;i--) if(used[10+i]) {
      used[c[i].a]=true;
      if(c[i].op!=2) used[c[i].b]=true;
    }
    for(int i=0;i<N;i++) if(c[i].op==2 && (!requireUsedNot || used[10+i])) hasNot=true;
    if(!hasNot) result+=10000;
  }
  return result;
}

Circuit randomCircuit() {
  Circuit c;
  for(int i=0;i<N;i++) c[i]={int(rng()%10==0?2:rng()%2),int(rng()%(10+i)),int(rng()%(10+i))};
  return c;
}

std::vector<Gate> witness() {
  std::array<std::vector<int>,10> nbrs;
  const std::array<bool,10> cover={false,true,false,true,true,true,true,true,false,false};
  for(auto [a,b]:edges) {
    if(!cover[a]) std::swap(a,b);
    nbrs[a].push_back(b);
  }
  std::vector<Gate> c;
  std::vector<int> stars;
  for(int i=0;i<10;i++) if(!nbrs[i].empty()) {
    int x=nbrs[i][0];
    for(size_t j=1;j<nbrs[i].size();j++) {c.push_back({1,x,nbrs[i][j]});x=9+c.size();}
    c.push_back({0,i,x});stars.push_back(9+c.size());
  }
  int x=stars[0];
  for(size_t i=1;i<stars.size();i++) {c.push_back({1,x,stars[i]});x=9+c.size();}
  return c;
}

Circuit nearWitness() {
  auto w=witness();
  if(w.size()!=20) { std::cerr << "bad witness size "<<w.size()<<"\n"; std::exit(2); }
  int remove=rng()%20;
  int replacement=(rng()%2)?w[remove].a:w[remove].b;
  Circuit c;int out=0;
  for(int i=0;i<20;i++) if(i!=remove) {
    auto g=w[i];
    auto remap=[&](int k) {return k==10+remove?replacement:k>10+remove?k-1:k;};
    g.a=remap(g.a);g.b=remap(g.b);c[out++]=g;
  }
  return c;
}

void dump(const Circuit& c, const std::string& path) {
  std::ofstream f(path);
  for(int i=0;i<N;i++) f<<10+i<<" "<<(c[i].op==0?"and":c[i].op==1?"or":"not")<<" "<<c[i].a<<" "<<c[i].b<<"\n";
}

int main(int argc,char**argv) {
  if(argc!=4) {std::cerr<<"usage: search seconds seed output-prefix\n";return 2;}
  int seconds=std::atoi(argv[1]);rng.seed(std::strtoull(argv[2],nullptr,10));std::string prefix=argv[3];
  requireNot=std::getenv("PNP_REQUIRE_NOT")!=nullptr;
  requireUsedNot=std::getenv("PNP_REQUIRE_USED_NOT")!=nullptr;
  for(int x=0;x<1024;x++) {
    for(int i=0;i<10;i++) if(x&(1<<i)) inputs[i][x/64]|=uint64_t(1)<<(x%64);
    for(auto [a,b]:edges) if((x&(1<<a))&&(x&(1<<b))) {target[x/64]|=uint64_t(1)<<(x%64);break;}
  }
  auto start=std::chrono::steady_clock::now();
  long iterations=0,restarts=0;int best=1025;
  while(std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<seconds) {
    Circuit c = rng()%4?nearWitness():randomCircuit();
    int weight=1+(rng()%16),value=score(c,weight),since=0;
    for(int step=0;step<100000;step++) {
      Circuit d=c;
      int mutations=1+(rng()%100<10?1+rng()%5:0);
      for(int k=0;k<mutations;k++) {
        int i=rng()%N,what=rng()%3;
        if(what==0) d[i].op=rng()%10==0?2:rng()%2;
        if(what==1) d[i].a=rng()%(10+i);
        if(what==2) d[i].b=rng()%(10+i);
      }
      int v=score(d,weight);iterations++;
      if(v<=value) {c=d;if(v<value)since=0;value=v;}
      since++;
      if(value<best) {
        best=value;dump(c,prefix+"-best.txt");
        std::cout<<"best="<<best<<" weight="<<weight<<" iterations="<<iterations<<" restarts="<<restarts<<" elapsed="<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<std::endl;
      }
      if(value==0) {dump(c,prefix+"-witness.txt");return 0;}
      if(since>20000) break;
      if(iterations%10000==0 && std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()>=seconds) break;
    }
    restarts++;
  }
  std::cout<<"DONE no witness iterations="<<iterations<<" restarts="<<restarts<<" best="<<best<<std::endl;
}
