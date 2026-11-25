#include <array>
#include <algorithm>
#include <bit>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <random>
#include <vector>
using TT=std::array<uint64_t,16>;
#ifndef CGP_GATES
#define CGP_GATES 19
#endif
#ifndef CGP_SIGNED
#define CGP_SIGNED 0
#endif
constexpr int N=CGP_GATES;
constexpr bool signed_basis=CGP_SIGNED;
struct Gate { int op,a,b; };
using Circ=std::array<Gate,N>;
std::array<TT,10> input;
TT target;
TT minimal;
int edgeweight=1,negativeweight=12;
const int edges[15][2]={{0,1},{1,2},{2,3},{3,4},{4,0},{0,5},{1,6},{2,7},{3,8},{4,9},{5,7},{7,9},{9,6},{6,8},{8,5}};
std::mt19937 rng;
int rnd(int n) {return rng()%n;}
int score(const Circ& c) {
  std::array<TT,10+N> w;
  std::copy(input.begin(),input.end(),w.begin());
  for(int g=0;g<N;++g) {
    const auto& x=c[g];
    for(int j=0;j<16;++j) w[g+10][j]=x.op==0?w[x.a][j]&w[x.b][j]:x.op==1?w[x.a][j]|w[x.b][j]:signed_basis?(x.op==2?w[x.a][j]&~w[x.b][j]:~w[x.a][j]&w[x.b][j]):~w[x.a][j];
  }
  int s=0;
  for(int j=0;j<16;++j) {auto x=w[9+N][j]^target[j];s+=__builtin_popcountll(x&target[j])+(edgeweight-1)*__builtin_popcountll(x&minimal[j])+negativeweight*__builtin_popcountll(x&~target[j]);}
  return s;
}
std::vector<Gate> monotone_seed() {
  std::vector<int> covers;
  for(int mask=0;mask<1024;++mask) if(__builtin_popcount((unsigned)mask)==6) {
    bool okay=true;
    for(auto& e:edges) if(!((mask>>e[0])&1)&&!((mask>>e[1])&1)) okay=false;
    if(okay) covers.push_back(mask);
  }
  int cover=covers[rnd(covers.size())];
  std::array<std::vector<int>,10> neigh;
  for(auto& e:edges) {
    int a=e[0],b=e[1];
    if(!((cover>>a)&1)||(((cover>>b)&1)&&rnd(2))) std::swap(a,b);
    neigh[a].push_back(b);
  }
  std::vector<Gate> c;
  auto add=[&](int op,int a,int b){c.push_back({op,a,b});return 9+(int)c.size();};
  std::vector<int> products;
  for(int i=0;i<10;++i) if(!neigh[i].empty()) {
    std::shuffle(neigh[i].begin(),neigh[i].end(),rng);
    int accum=neigh[i][0];
    for(size_t j=1;j<neigh[i].size();++j) accum=add(1,accum,neigh[i][j]);
    products.push_back(add(0,i,accum));
  }
  std::shuffle(products.begin(),products.end(),rng);
  int accum=products[0];
  for(size_t i=1;i<products.size();++i) accum=add(1,accum,products[i]);
  return c;
}
Circ seed() {
  auto c=monotone_seed();
  if(c.size()!=20) {fprintf(stderr,"seed size %zu\n",c.size());exit(2);}
  while(c.size()>N) {
    int cut=rnd(c.size()),replacement=rnd(2)?c[cut].a:c[cut].b;
    c.erase(c.begin()+cut);
    for(auto& g:c) for(int* p:{&g.a,&g.b}) {if(*p==10+cut) *p=replacement; else if(*p>10+cut) --*p;}
  }
  Circ r;std::copy(c.begin(),c.end(),r.begin());
  return r;
}
void print(const Circ& c,int s,uint64_t it,int restart) {
  printf("score=%d iteration=%llu restart=%d gates=[",s,(unsigned long long)it,restart);
  for(int g=0;g<N;++g) printf("%s[%d,%d,%d]",g?",":"",c[g].op,c[g].a,c[g].b);
  printf("]\n");fflush(stdout);
}
int main(int argc,char** argv) {
  int seconds=argc>1?atoi(argv[1]):600,randomseed=argc>2?atoi(argv[2]):0;double anneal=argc>3?atof(argv[3]):0;rng.seed(randomseed);
  edgeweight=argc>4?atoi(argv[4]):1;negativeweight=argc>5?atoi(argv[5]):12;
  int forcednot=argc>7?atoi(argv[7]):0;bool loaded=argc>6;Circ initial;
  if(loaded) {
    FILE* f=fopen(argv[6],"r");if(!f)return 3;
    for(auto& g:initial)if(fscanf(f,"%d %d %d",&g.op,&g.a,&g.b)!=3)return 4;
    fclose(f);
  }
  for(int x=0;x<1024;++x) {
    for(int i=0;i<10;++i) if((x>>i)&1) input[i][x/64]|=uint64_t(1)<<(x%64);
    bool yes=false;for(auto& e:edges) if(((x>>e[0])&1)&&((x>>e[1])&1)) yes=true;
    if(yes) target[x/64]|=uint64_t(1)<<(x%64);
    if(yes&&__builtin_popcount((unsigned)x)==2) minimal[x/64]|=uint64_t(1)<<(x%64);
  }
  auto end=std::chrono::steady_clock::now()+std::chrono::seconds(seconds);
  int global=100000;uint64_t it=0;int restart=0;
  while(std::chrono::steady_clock::now()<end) {
    Circ best=loaded&&rnd(4)?initial:seed();
    if(forcednot) {int ns=0;for(auto& g:best)ns+=g.op==2;if(!ns)best[rnd(N)].op=2;}
    int bs=score(best),stale=0;
    for(int step=0;step<300000&&stale<60000;++step,++it) {
      Circ c=best;int mutations=1+(rnd(100)<15?rnd(5):0);
      for(int j=0;j<mutations;++j) {
        int g=rnd(N),field=rnd(3);
        if(field==0) c[g].op=rnd(signed_basis?4:3);else if(field==1)c[g].a=rnd(g+10);else c[g].b=rnd(g+10);
      }
      if(forcednot) {int ns=0;for(auto& g:c)ns+=g.op==2;if(ns!=1)continue;}
      if(forcednot>=2) {
        unsigned used=1u<<(N-1);
        for(int k=N-1;k>=0;--k)if(used&(1u<<k)) {
          if(c[k].a>=10)used|=1u<<(c[k].a-10);
          if(c[k].op!=2&&c[k].b>=10)used|=1u<<(c[k].b-10);
        }
        bool deadnot=false;for(int k=0;k<N;++k)if(c[k].op==2&&!(used&(1u<<k)))deadnot=true;
        if(deadnot)continue;
      }
      int s=score(c);
      double temperature=anneal*std::pow(0.01,double(step%100000)/100000.0);
      if(s<=bs || (anneal>0 && double(rng())/rng.max()<std::exp(double(bs-s)/temperature))) {if(s<bs)stale=0;best=c;bs=s;}
      ++stale;
      if(s<global){global=s;print(c,s,it,restart);}
      if(s==0){print(c,s,it,restart);return 0;}
      if((it&65535)==0&&std::chrono::steady_clock::now()>=end)break;
    }
    ++restart;
  }
  printf("finished minimum_score=%d iterations=%llu restarts=%d\n",global,(unsigned long long)it,restart);return 0;
}
