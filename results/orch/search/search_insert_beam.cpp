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

#include <set>
TT table(const Circuit&c){TT ws[29];for(int i=0;i<10;i++)ws[i]=inputs[i];for(int j=0;j<19;j++){auto g=c[j];for(int k=0;k<16;k++)ws[j+10][k]=g.op==0?(ws[g.a][k]&ws[g.b][k]):g.op==1?(ws[g.a][k]|ws[g.b][k]):~ws[g.a][k];}return ws[28];}
int main(int argc,char **argv){
 for(int r=0;r<1024;r++){
  for(int i=0;i<10;i++)if((r>>i)&1)inputs[i][r/64]|=1ull<<(r%64);
  bool good=false;for(auto&e:edges)if((r>>e[0])&(r>>e[1])&1)good=true;
  if(good)target[r/64]|=1ull<<(r%64);
 }
 FILE*f=fopen(argv[1],"r");Gate base[18];int ignored[3];fscanf(f,"%d%d%d",&ignored[0],&ignored[1],&ignored[2]);
 for(auto&g:base){fscanf(f,"%d%d%d",&g.op,&g.a,&g.b);if(g.a>10)--g.a;if(g.b>10)--g.b;}

 int best=1024;uint64_t trials=0;
 struct Entry{int sc;Circuit c;int p;};std::vector<Entry> pool;std::set<TT> seen;
 for(int p=0;p<18;p++)for(int neg=0;neg<10+p;neg++){
  Circuit c;for(int j=0;j<18;j++){auto g=base[j];if(g.a>=10+p)++g.a;if(g.b>=10+p)++g.b;c[j+(j>=p)]=g;}c[p]={2,neg,neg};
  for(int j=p+1;j<19;j++)for(int op=0;op<2;op++)for(int other=0;other<10+j;other++){
   Circuit d=c;d[j]={op,p+10,other};int sc=score(d);++trials;
   if(sc<=40&&seen.insert(table(d)).second)pool.push_back({sc,d,p});
  }
 }
 std::sort(pool.begin(),pool.end(),[](auto&a,auto&b){return a.sc<b.sc;});
 printf("POOL %zu\n",pool.size());fflush(stdout);
 if(pool.size()>1500)pool.resize(1500);
 for(int z=0;z<(int)pool.size();z++){
  auto e=pool[z];
  for(int j=0;j<19;j++)if(j!=e.p)for(int op=0;op<2;op++)for(int a=0;a<10+j;a++)for(int b=a+1;b<10+j;b++){
   Circuit d=e.c;d[j]={op,a,b};int sc=score(d);++trials;
   if(sc<best){best=sc;printf("BEST %d beam %d changed %d trials %llu\n",sc,z,j,(unsigned long long)trials);print(d);}
   if(best==0)return 0;
  }
 }
 printf("END best=%d trials=%llu\n",best,(unsigned long long)trials);
}
