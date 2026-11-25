#include <array>
#include <vector>
#include <cstdint>
#include <cstdio>
#include <random>
#include <algorithm>
#include <chrono>
using TT = std::array<uint64_t,16>;
struct Gate { int op,a,b; };
using Circuit = std::array<Gate,19>;
const std::array<std::pair<int,int>,15> edges={{{0,1},{1,2},{2,3},{3,4},{4,0},{0,5},{1,6},{2,7},{3,8},{4,9},{5,7},{7,9},{9,6},{6,8},{8,5}}};
std::array<TT,30> wires;
TT target;
std::mt19937 rng(2592);
int score(const Circuit &c) {
 for(int g=0;g<19;++g) {
  for(int w=0;w<16;++w) {
   auto a=wires[c[g].a][w],b=wires[c[g].b][w];
   wires[10+g][w]=c[g].op==0?a&b:c[g].op==1?a|b:~a;
  }
 }
 int cost=0;
 for(int w=0;w<16;++w)cost+=__builtin_popcountll(wires[28][w]^target[w]);
 return cost;
}
void print(const Circuit &c,int cost) {
 printf("score %d\n",cost);
 for(int i=0;i<19;++i)printf("%d %c %d %d\n",10+i,c[i].op==0?'&':c[i].op==1?'|':'!',c[i].a,c[i].b);
 fflush(stdout);
}
std::vector<Gate> seed() {
 std::vector<int> independent;
 for(int mask=0;mask<1024;++mask) {
  if(__builtin_popcount(unsigned(mask))!=4)continue;
  bool okay=true;
  for(auto [a,b]:edges)if((mask>>a&1)&&(mask>>b&1))okay=false;
  if(okay)independent.push_back(mask);
 }
 int mask=independent[rng()%independent.size()];
 std::array<std::vector<int>,10> stars;
 for(auto [a,b]:edges) {
  if(mask>>a&1)stars[b].push_back(a);
  else if(mask>>b&1)stars[a].push_back(b);
  else if(rng()%2)stars[a].push_back(b);
  else stars[b].push_back(a);
 }
 std::vector<Gate> gates;
 std::vector<int> terms;
 std::vector<int> order;
 for(int a=0;a<10;++a)if(!stars[a].empty())order.push_back(a);
 std::shuffle(order.begin(),order.end(),rng);
 for(int a:order){
  std::shuffle(stars[a].begin(),stars[a].end(),rng);
  int w=stars[a][0];
  for(unsigned j=1;j<stars[a].size();++j){gates.push_back({1,w,stars[a][j]});w=9+gates.size();}
  gates.push_back({0,a,w});terms.push_back(9+gates.size());
 }
 std::shuffle(terms.begin(),terms.end(),rng);
 int w=terms[0];
 for(unsigned j=1;j<terms.size();++j){gates.push_back({1,w,terms[j]});w=9+gates.size();}
 return gates;
}
Circuit reduce(const std::vector<Gate> &gates) {
 int remove=rng()%gates.size();
 int replace=rng()%2?gates[remove].a:gates[remove].b;
 Circuit c{};
 int j=0;
 for(unsigned i=0;i<gates.size();++i){
  if(i==unsigned(remove))continue;
  auto g=gates[i];
  auto fix=[&](int w){if(w==remove+10)w=replace;return w>remove+10?w-1:w;};
  g.a=fix(g.a);g.b=fix(g.b);
  if(j<19)c[j++]=g;
 }
 while(j<19){c[j]={1,9+j,9+j};++j;}
 return c;
}
int main(int argc,char **argv) {
 int seconds=argc>1?atoi(argv[1]):300;
 for(int x=0;x<1024;++x){
  for(int a=0;a<10;++a)if(x>>a&1)wires[a][x/64]|=uint64_t(1)<<(x%64);
  bool f=false;for(auto [a,b]:edges)if((x>>a&1)&&(x>>b&1))f=true;
  if(f)target[x/64]|=uint64_t(1)<<(x%64);
 }
 auto end=std::chrono::steady_clock::now()+std::chrono::seconds(seconds);
 int best=1024;
 uint64_t evaluations=0,restarts=0;
 Circuit champion{};
 while(std::chrono::steady_clock::now()<end){
  Circuit current=reduce(seed());
  if(restarts%3==0 && best<30){current=champion;for(int k=0;k<3;++k){int g=rng()%19;current[g]={int(rng()%3),int(rng()%(10+g)),int(rng()%(10+g))};}}
  int cost=score(current);
  for(int iteration=0,stale=0;iteration<2000&&stale<400;++iteration){
   Circuit next=current;
   int g=rng()%19,which=rng()%3;
   if(which==0)next[g].op=rng()%3;
   else if(which==1)next[g].a=rng()%(10+g);
   else next[g].b=rng()%(10+g);
   int value=score(next);++evaluations;
   if(value<cost || (value==cost && rng()%4==0)){
    current=next;stale=value<cost?0:stale+1;cost=value;
   }else ++stale;
   if(cost<best){best=cost;champion=current;printf("restart %llu evaluation %llu ", (unsigned long long)restarts,(unsigned long long)evaluations);print(current,cost);}
   if(cost==0)return 0;
  }
  ++restarts;
 }
 printf("DONE restarts=%llu evaluations=%llu best=%d\n",(unsigned long long)restarts,(unsigned long long)evaluations,best);
 print(champion,best);
}
