#include <array>
#include <vector>
#include <random>
#include <chrono>
#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <algorithm>
using TT = std::array<unsigned long long,16>;
struct Gate { int op,a,b; };
std::mt19937 rng(2373);
std::array<TT,30> vals;
TT target;
std::vector<std::pair<int,int>> edges{{0,1},{1,2},{2,3},{3,4},{4,0},{0,5},{1,6},{2,7},{3,8},{4,9},{5,7},{7,9},{9,6},{6,8},{8,5}};
int score(const std::vector<Gate>& gs) {
 for (int k=0;k<(int)gs.size();++k) {
  auto g=gs[k];
  for(int w=0;w<16;++w) vals[10+k][w]=g.op==0?(vals[g.a][w]&vals[g.b][w]):g.op==1?(vals[g.a][w]|vals[g.b][w]):~vals[g.a][w];
 }
 int s=0;
 for(int w=0;w<16;++w) {auto z=vals[9+gs.size()][w]; s+=__builtin_popcountll(z&~target[w])*8+__builtin_popcountll(~z&target[w]);}
 return s;
}
std::vector<Gate> seed() {
 std::vector<std::vector<int>> covers;
 for(int m=0;m<1024;++m) if(__builtin_popcount((unsigned)m)==6) {
  bool ok=true;for(auto [a,b]:edges)if(!((m>>a&1)||(m>>b&1)))ok=false;
  if(ok) {std::vector<int>s;for(int a=0;a<10;++a)if(m>>a&1)s.push_back(a);covers.push_back(s);}
 }
 auto cover=covers[rng()%covers.size()];std::shuffle(cover.begin(),cover.end(),rng);
 std::array<std::vector<int>,10> neighbors;
 for(auto [a,b]:edges) {
  bool ca=std::find(cover.begin(),cover.end(),a)!=cover.end();
  bool cb=std::find(cover.begin(),cover.end(),b)!=cover.end();
  if(ca&&(!cb||(rng()&1)))neighbors[a].push_back(b); else neighbors[b].push_back(a);
 }
 std::vector<Gate> gs;std::vector<int>stars;
 for(int a:cover)if(!neighbors[a].empty()) {
  auto ns=neighbors[a];std::shuffle(ns.begin(),ns.end(),rng);int last=ns[0];
  for(int k=1;k<(int)ns.size();++k) {gs.push_back({1,last,ns[k]});last=9+gs.size();}
  gs.push_back({0,a,last});stars.push_back(9+gs.size());
 }
 std::shuffle(stars.begin(),stars.end(),rng);int last=stars[0];
 for(int k=1;k<(int)stars.size();++k) {gs.push_back({1,last,stars[k]});last=9+gs.size();}
 if(gs.size()!=20) {std::fprintf(stderr,"Unexpected seed size %zu\n",gs.size());std::exit(2);}
 int d=rng()%19; int replacement=(rng()&1)?gs[d].a:gs[d].b;
 gs.erase(gs.begin()+d);
 for(int k=d;k<19;++k) {
  if(gs[k].a==10+d) gs[k].a=replacement;
  else if(gs[k].a>10+d)--gs[k].a;
  if(gs[k].b==10+d) gs[k].b=replacement;
  else if(gs[k].b>10+d)--gs[k].b;
 }
 return gs;
}
void print(const std::vector<Gate>&gs,int s,long long iter) {
 printf("score=%d iteration=%lld\n",s,iter);
 for(int k=0;k<(int)gs.size();++k)printf("%d %s %d %d\n",10+k,gs[k].op==0?"and":gs[k].op==1?"or":"not",gs[k].a,gs[k].b);
 fflush(stdout);
}
int main(int argc,char**argv) {
 int seconds=argc>1?atoi(argv[1]):600;
 if(argc>2)rng.seed(atoi(argv[2]));
 double scale=argc>3?atof(argv[3]):1.0;
 for(int x=0;x<1024;++x) {
  for(int a=0;a<10;++a)if(x>>a&1)vals[a][x/64]|=1ull<<(x%64);
  bool hit=false;for(auto [a,b]:edges)if((x>>a&1)&&(x>>b&1))hit=true;
  if(hit)target[x/64]|=1ull<<(x%64);
 }
 auto start=std::chrono::steady_clock::now();
 int best=100000;long long total=0;int restarts=0;
 while(std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<seconds) {
  auto gs=seed();int current=score(gs);double temp=scale*(1.0+(rng()%100)/25.0);
  ++restarts;
  for(int step=0;step<250000;++step) {
   ++total; int k=rng()%19;auto old=gs[k];int mutation=rng()%9;
   if(mutation==0&&k!=18)gs[k].op=rng()%3;
   else if(mutation<5)gs[k].a=rng()%(10+k);
   else gs[k].b=rng()%(10+k);
   int next=score(gs);
   if(next<=current||std::generate_canonical<double,32>(rng)<std::exp((current-next)/temp)) current=next;
   else gs[k]=old;
   if(current<best) {best=current; print(gs,best,total);if(!best)return 0;}
   if(step%25000==0)temp*=0.82;
  }
 }
 printf("Finished restarts=%d evaluations=%lld best=%d\n",restarts,total,best);
}
