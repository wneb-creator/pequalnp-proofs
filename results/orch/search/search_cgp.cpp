#include <array>
#include <algorithm>
#include <bit>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <random>
#include <vector>

using TT=std::array<uint64_t,16>;
struct Gate { int op,a,b; };
using Circuit=std::array<Gate,19>;
std::mt19937_64 rng(1932592);
TT inputs[10],target,weightmask[4];
int edges[15][2]={{0,1},{1,2},{2,3},{3,4},{4,0},{0,5},{1,6},{2,7},{3,8},{4,9},{5,7},{7,9},{9,6},{6,8},{8,5}};
int score(const Circuit &c, int mode=0) {
 TT wires[29];
 for(int i=0;i<10;i++) wires[i]=inputs[i];
 for(int j=0;j<19;j++) {
  auto g=c[j]; auto &w=wires[j+10],&a=wires[g.a],&b=wires[g.b];
  for(int k=0;k<16;k++) w[k]=g.op==0?(a[k]&b[k]):g.op==1?(a[k]|b[k]):~a[k];
 }
 int s=0;
 for(int k=0;k<16;k++) {
  auto e=wires[28][k]^target[k];
  s+=std::popcount(e);
  if(mode) s+=3*std::popcount(e&weightmask[mode-1][k]);
 }
 return s;
}
void print(const Circuit &c) {
 for(int j=0;j<19;j++) printf("%d %d %d %d\n",10+j,c[j].op,c[j].a,c[j].b);
 fflush(stdout);
}
Circuit randomCircuit() {
 Circuit c;
 for(int j=0;j<19;j++) c[j]={(int)(rng()%10<1?2:rng()%2),(int)(rng()%(j+10)),(int)(rng()%(j+10))};
 return c;
}
Circuit seed() {
 std::vector<int> perm(10); for(int i=0;i<10;i++)perm[i]=i;
 // A random maximum independent set determines a six-vertex cover.
 int ind[5][4]={{0,2,8,9},{0,3,6,7},{1,3,5,9},{1,4,7,8},{2,4,5,6}};
 bool covered[10];for(auto &b:covered)b=true;
 int si=rng()%5; for(int x:ind[si])covered[x]=false;
 std::vector<int> nb[10];
 for(auto &e:edges) {
  int a=e[0],b=e[1]; if(!covered[a]||(covered[b]&&rng()%2))std::swap(a,b);
  nb[a].push_back(b);
 }
 std::shuffle(perm.begin(),perm.end(),rng);
 std::vector<Gate> gs;
 std::vector<int> stars;
 for(int a:perm) if(!nb[a].empty()) {
  std::shuffle(nb[a].begin(),nb[a].end(),rng);
  int acc=nb[a][0];
  for(int k=1;k<(int)nb[a].size();k++){gs.push_back({1,acc,nb[a][k]});acc=9+gs.size();}
  gs.push_back({0,a,acc});stars.push_back(9+gs.size());
 }
 std::shuffle(stars.begin(),stars.end(),rng);
 int acc=stars[0];for(int k=1;k<(int)stars.size();k++){gs.push_back({1,acc,stars[k]});acc=9+gs.size();}
 // Delete one of the twenty gates, rewire consumers to one of its arguments.
 int del=rng()%gs.size(),replace=rng()%2?gs[del].a:gs[del].b;
 Circuit c=randomCircuit();
 int at=0;
 for(int j=0;j<(int)gs.size();j++) if(j!=del) {
  auto g=gs[j];
  for(auto p:{&g.a,&g.b}){if(*p==del+10)*p=replace;if(*p>del+10)--*p;}
  c[at++]=g;
 }
 return c;
}
int main(int argc,char **argv) {
 int seconds=argc>1?atoi(argv[1]):600; uint64_t iterations=0;
 if(argc>2)rng.seed(strtoull(argv[2],nullptr,10));
 for(int r=0;r<1024;r++) {
  for(int i=0;i<10;i++)if((r>>i)&1)inputs[i][r/64]|=1ull<<(r%64);
  bool good=false;for(auto&e:edges)if((r>>e[0])&(r>>e[1])&1)good=true;
  if(good)target[r/64]|=1ull<<(r%64);
  if(std::popcount((unsigned)r)==2)weightmask[0][r/64]|=1ull<<(r%64);
  if(!good)weightmask[1][r/64]|=1ull<<(r%64);
  if(std::popcount((unsigned)r)<=4)weightmask[2][r/64]|=1ull<<(r%64);
 }
 auto start=std::chrono::steady_clock::now();int best=1024;
 std::vector<Circuit> elites;
 for(int run=0;;run++) {
  Circuit cur=run%3==0?seed():elites.empty()?randomCircuit():elites[rng()%elites.size()];
  int mode=run%4, sc=score(cur,mode), stagnation=0;
  for(int it=0;it<1000000;it++) {
   Circuit next=cur;
   int mutations=rng()%100<90?1:2+(rng()%4);
   for(int m=0;m<mutations;m++) {
    int j=rng()%19,kind=rng()%3;
    if(kind==0)next[j].op=rng()%10==0?2:rng()%2;
    else if(kind==1)next[j].a=rng()%(j+10);
    else next[j].b=rng()%(j+10);
   }
   int ns=score(next,mode);++iterations;
   if(ns<=sc){cur=next;if(ns<sc)stagnation=0;sc=ns;}
   ++stagnation;
   if(sc<best*4) {
    int plain=score(cur);
    if(plain<best) {
     best=plain;printf("BEST %d run %d iter %llu elapsed %.1f\n",best,run,(unsigned long long)iterations,std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()); print(cur);
     elites.push_back(cur);if(elites.size()>30)elites.erase(elites.begin());
     if(best==0)return 0;
    }
   }
   if(stagnation>100000)break;
   if(iterations%10000==0&&std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()>seconds){printf("END best=%d iterations=%llu\n",best,(unsigned long long)iterations);return 1;}
  }
 }
}
