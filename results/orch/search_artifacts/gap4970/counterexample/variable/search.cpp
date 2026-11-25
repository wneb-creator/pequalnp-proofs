#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <random>
#include <string>
#include <vector>
using U=uint64_t;
constexpr int N=11,P=5,L=6,G=28,W=32,V=N+G;
constexpr unsigned FULL=(1u<<N)-1,POINTS=(1u<<P)-1,LINES=FULL^POINTS;
struct Gate{int op,a,b;};
struct Graph{U key=~U(0),truth[W]{};unsigned adj[N]{},cover=0;int matching[P]{},m=0,tau=0,rect=0;};
struct Stats{int wrong=0,miss=0,mix=0,cost=0,m=0,tau=0,rect=0;int margin()const{return cost-m-tau+1;}bool valid()const{return !wrong&&!miss&&!mix&&!rect&&m;}};
struct Circ{std::array<Gate,G>gs;U w[V][W]{},cone[V]{},cov[G]{},keep=0,key=0;unsigned sup[V]{},reach[V]{};int out=0;Stats st;};
std::array<Graph,16384>cache;
U raw[N][W]{},pairtruth[P*L][W]{};
std::vector<std::pair<std::vector<Gate>,int>>seeds;
std::mt19937_64 rng(497020);
int rnd(int x){assert(x>0);return rng()%x;}
bool bit(const U*w,unsigned r){return w[r/64]>>(r%64)&1;}
bool augment(int a,Graph&h,int*owner,bool*seen){for(int b=0;b<L;b++)if((h.adj[a]>>(P+b)&1)&&!seen[b]){seen[b]=true;if(owner[b]<0||augment(owner[b],h,owner,seen)){owner[b]=a;return true;}}return false;}
Graph&graph(U key){
 auto&h=cache[(key*11400714819323198485ull)>>50];if(h.key==key)return h;h=Graph();h.key=key;h.m=std::popcount(key);
 for(int a=0;a<P;a++)for(int b=0;b<L;b++)if(key>>(a*L+b)&1){h.adj[a]|=1u<<(P+b);h.adj[P+b]|=1u<<a;for(int k=0;k<W;k++)h.truth[k]|=pairtruth[a*L+b][k];}
 for(int a=0;a<P;a++)for(int b=a+1;b<P;b++){int d=std::popcount(h.adj[a]&h.adj[b]);h.rect+=d*(d-1)/2;}
 int owner[L];std::fill(owner,owner+L,-1);std::fill(h.matching,h.matching+P,-1);for(int a=0;a<P;a++){bool seen[L]{};h.tau+=augment(a,h,owner,seen);}
 for(int b=0;b<L;b++)if(owner[b]>=0)h.matching[owner[b]]=P+b;
 unsigned seenA=0,seenB=0;for(int a=0;a<P;a++)if(h.matching[a]<0)seenA|=1u<<a;
 for(;;){unsigned oldA=seenA,oldB=seenB;for(int a=0;a<P;a++)if(seenA>>a&1)for(int b=0;b<L;b++)if((h.adj[a]>>(P+b)&1)&&h.matching[a]!=P+b)seenB|=1u<<b;for(int b=0;b<L;b++)if((seenB>>b&1)&&owner[b]>=0)seenA|=1u<<owner[b];if(oldA==seenA&&oldB==seenB)break;}
 h.cover=(POINTS^seenA)|(seenB<<P);assert(std::popcount(h.cover)==h.tau);for(int a=0;a<P;a++)for(int b=0;b<L;b++)if(key>>(a*L+b)&1)assert((h.cover>>a&1)||(h.cover>>(P+b)&1));return h;
}
void setup(const char*path){
 for(unsigned row=0;row<=FULL;row++)for(int i=0;i<N;i++)if(row>>i&1)raw[i][row/64]|=U(1)<<(row%64);
 for(int a=0;a<P;a++)for(int b=0;b<L;b++)for(int k=0;k<W;k++)pairtruth[a*L+b][k]=raw[a][k]&raw[P+b][k];
 std::ifstream f(path);int count;f>>count;assert(f&&count>0);for(int z=0;z<count;z++){int size,out;f>>size>>out;assert(size<=G);std::vector<Gate>gs(size);for(auto&g:gs)f>>g.op>>g.a>>g.b;assert(f);seeds.push_back({gs,out});}
}
void eval(Circ&c,int start=0){
 for(int j=start;j<G;j++){auto g=c.gs[j];int v=N+j;assert(g.a<v&&g.b<v);for(int k=0;k<W;k++)c.w[v][k]=g.op?(c.w[g.a][k]|c.w[g.b][k]):(c.w[g.a][k]&c.w[g.b][k]);c.sup[v]=g.op?(c.sup[g.a]|c.sup[g.b]):(c.sup[g.a]&c.sup[g.b]);c.reach[v]=g.op?(c.reach[g.a]|c.reach[g.b]):0;c.cone[v]=c.cone[g.a]|c.cone[g.b]|(U(1)<<j);}
 c.key=0;for(int a=0;a<P;a++)for(int b=0;b<L;b++)if(bit(c.w[c.out],(1u<<a)|(1u<<(P+b))))c.key|=U(1)<<(a*L+b);auto&h=graph(c.key);c.st={};c.st.m=h.m;c.st.tau=h.tau;c.st.rect=h.rect;
 for(int k=0;k<W;k++)c.st.wrong+=std::popcount(c.w[c.out][k]^h.truth[k]);
 for(int j=0;j<G;j++){c.cov[j]=0;unsigned q=c.sup[N+j];if(!c.gs[j].op||std::popcount(q)<2||bit(c.w[N+j],FULL^q))continue;for(int v=0;v<N;v++)if(!(q&~h.adj[v])){if(v<P){for(int b=0;b<L;b++)if(q>>(P+b)&1)c.cov[j]|=U(1)<<(v*L+b);}else{for(int a=0;a<P;a++)if(q>>a&1)c.cov[j]|=U(1)<<(a*L+v-P);}}}
 c.keep=c.cone[c.out];U covered=0;for(int j=0;j<G;j++)if(c.keep>>j&1)covered|=c.cov[j];
 while((covered&c.key)!=c.key){int chosen=-1,benefit=0,cost=1;for(int j=0;j<G;j++){int b=std::popcount(c.cov[j]&~covered),d=std::popcount(c.cone[N+j]&~c.keep);if(b&&d&&(chosen<0||b*cost>benefit*d)){chosen=j;benefit=b;cost=d;}}if(chosen<0)break;c.keep|=c.cone[N+chosen];for(int j=0;j<G;j++)if(c.keep>>j&1)covered|=c.cov[j];}
 c.st.miss=std::popcount(c.key&~covered);c.st.cost=std::popcount(c.keep);for(int j=0;j<G;j++)if(c.keep>>j&1)c.st.mix+=c.gs[j].op&&(c.reach[N+j]&POINTS)&&(c.reach[N+j]&LINES);
}
void reorder(Circ&c){std::array<Gate,G>old=c.gs;int map[V];std::fill(map,map+V,-1);for(int i=0;i<N;i++)map[i]=i;std::vector<int>todo;for(int i=0;i<G;i++)todo.push_back(i);for(int t=0;t<G;t++){std::vector<int>ready;for(unsigned j=0;j<todo.size();j++)if(map[old[todo[j]].a]>=0&&map[old[todo[j]].b]>=0)ready.push_back(j);int z=ready[rnd(ready.size())],j=todo[z];auto g=old[j];c.gs[t]={g.op,map[g.a],map[g.b]};map[N+j]=N+t;todo.erase(todo.begin()+z);}c.out=map[c.out];}
Circ seed(int index=-1){Circ c;for(int i=0;i<N;i++){c.sup[i]=c.reach[i]=1u<<i;std::copy(raw[i],raw[i]+W,c.w[i]);}auto[gs,out]=seeds[index<0?rnd(seeds.size()):index];c.out=out;for(unsigned j=0;j<gs.size();j++)c.gs[j]=gs[j];for(int j=gs.size();j<G;j++){int mode=rnd(4);if(mode==0){int a=rnd(N+j);c.gs[j]={0,a,a};}else if(mode==1)c.gs[j]={1,P+rnd(L),P+rnd(L)};else if(mode==2)c.gs[j]={1,rnd(P),rnd(P)};else c.gs[j]={0,rnd(P),P+rnd(L)};}if(index<0)reorder(c);eval(c);return c;}
double score(const Stats&s,int lane){double error=std::sqrt(double(s.wrong));double density=0.09*s.m+0.1*s.tau;double margin=s.margin();if(lane==0)return 3*error+8*s.miss+8*s.mix+8*s.rect+margin-density;if(lane==1)return 8*error+3*s.miss+3*s.mix+12*s.rect+margin-density;if(lane==2)return 3*error+12*s.miss+12*s.mix+3*s.rect+margin-density;return 4*error+6*s.miss+6*s.mix+10*s.rect+0.5*margin-0.3*s.m;}
void save(const Circ&c,const std::string&prefix){
 auto&h=graph(c.key);std::ofstream gf(prefix+".graph.json");gf<<"{\"name\":\"derived_variable_graph\",\"n\":"<<N<<",\"p\":"<<P<<",\"l\":"<<L<<",\"edges\":[";bool first=true;for(int a=0;a<P;a++)for(int b=0;b<L;b++)if(c.key>>(a*L+b)&1){if(!first)gf<<',';first=false;gf<<'['<<a<<','<<P+b<<']';}gf<<"],\"tau\":"<<h.tau<<",\"cover_mask\":"<<h.cover<<",\"matching\":[";first=true;for(int a=0;a<P;a++)if(h.matching[a]>=0){if(!first)gf<<',';first=false;gf<<'['<<a<<','<<h.matching[a]<<']';}gf<<"]}\n";
 int map[V];for(int i=0;i<N;i++)map[i]=i;std::fill(map+N,map+V,-1);std::vector<Gate>gs;for(int j=0;j<G;j++)if(c.keep>>j&1){auto g=c.gs[j];assert(map[g.a]>=0&&map[g.b]>=0);map[N+j]=N+gs.size();gs.push_back({g.op,map[g.a],map[g.b]});}assert(map[c.out]>=0);std::ofstream cf(prefix+".circuit.json");cf<<"{\"gates\":[";for(unsigned j=0;j<gs.size();j++){auto g=gs[j];if(j)cf<<',';cf<<'['<<g.op<<','<<g.a<<','<<g.b<<']';}cf<<"],\"output\":"<<map[c.out]<<",\"wrong_rows\":"<<c.st.wrong<<",\"missing_star_edges\":"<<c.st.miss<<",\"tCount\":"<<c.st.mix<<",\"rectangles\":"<<c.st.rect<<",\"margin\":"<<c.st.margin()<<"}\n";
}
void print(const Circ&c,unsigned long long it,double sec,const char*kind){auto&s=c.st;std::printf("%s seconds=%.3f iterations=%llu E=%d tau=%d gates=%d margin=%d wrong=%d missing=%d mixed=%d rectangles=%d key=%llu\n",kind,sec,it,s.m,s.tau,s.cost,s.margin(),s.wrong,s.miss,s.mix,s.rect,(unsigned long long)c.key);std::fflush(stdout);}
int main(int argc,char**argv){if(argc<4){std::fprintf(stderr,"usage: search SEEDS.dat SECONDS OUTPUT_PREFIX [RNG_SEED]\n");return 2;}if(argc>4)rng.seed(std::strtoull(argv[4],nullptr,10));setup(argv[1]);int seconds=std::atoi(argv[2]);std::string prefix=argv[3];auto stop=std::filesystem::path(argv[1]).parent_path().parent_path().parent_path()/"STOP";auto local=std::filesystem::path(argv[1]).parent_path()/"STOP";
 for(unsigned z=0;z<seeds.size();z++){auto c=seed(z);print(c,0,0,"CONTROL");assert(c.st.valid());save(c,prefix+".control"+std::to_string(z));}if(!seconds)return 0;
 std::vector<Circ>pop;for(int i=0;i<64;i++)pop.push_back(seed());Circ best=pop[0],bestValid=best;double bestScore=score(best.st,0),sec=0,next=60;int validMargin=best.st.margin(),validEdges=best.st.m;unsigned long long it=0;auto start=std::chrono::steady_clock::now();bool stopped=false;
 for(;;it++){if(it%4096==0){sec=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();if(std::filesystem::exists(stop)||std::filesystem::exists(local)){stopped=true;break;}if(sec>=seconds)break;if(sec>=next){print(best,it,sec,"STATUS_BEST");print(bestValid,it,sec,"STATUS_VALID");next+=60;}}
  int slot=rnd(pop.size()),lane=slot%4;Circ c=pop[slot];int first=G;if(rnd(1000)==0){reorder(c);first=0;}else{int changes=1+(rnd(100)<20)+(rnd(100)<3?rnd(5):0);for(int z=0;z<changes;z++){int j=rnd(G),mode=rnd(10);first=std::min(first,j);if(mode==0)c.gs[j].op^=1;else if(mode<5)c.gs[j].a=rnd(N+j);else if(mode<9)c.gs[j].b=rnd(N+j);else c.gs[j]=pop[rnd(pop.size())].gs[j];}if(rnd(100)<2)c.out=rnd(V);}eval(c,first);
  double before=score(pop[slot].st,lane),after=score(c.st,lane),temp=(slot/4)%8==0?2.0:(slot/4)%8==1?0.5:(slot/4)%8==2?0.1:0.0;if(after<=before||(temp&&double(rng())/double(UINT64_MAX)<std::exp((before-after)/temp)))pop[slot]=c;
  double sc=score(c.st,0);if(sc<bestScore){bestScore=sc;best=c;print(c,it,sec,"BEST");save(c,prefix+".best");}
  if(c.st.valid()&&(c.st.margin()<validMargin||(c.st.margin()==validMargin&&c.st.m>validEdges))){validMargin=c.st.margin();validEdges=c.st.m;bestValid=c;print(c,it,sec,"BEST_VALID");save(c,prefix+".valid");}
  if(c.st.valid()&&c.st.margin()<0){save(c,prefix+".counterexample");print(c,it,sec,"COUNTEREXAMPLE_REQUIRES_INDEPENDENT_CHECK");return 10;}
  if(it%32768==0)pop[rnd(pop.size())]=seed();if(it%131072==0)pop[rnd(pop.size())]=bestValid;
 }print(best,it,sec,"FINAL_BEST");print(bestValid,it,sec,"FINAL_VALID");save(bestValid,prefix+".final-valid");std::printf("%s no_counterexample\n",stopped?"STOPPED":"DONE");return stopped?75:0;}
