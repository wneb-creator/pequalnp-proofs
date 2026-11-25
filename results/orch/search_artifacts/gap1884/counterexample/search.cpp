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
using U=uint64_t;using TT=std::array<U,16>;
constexpr int N=11,G=18,MAXG=32;
struct Gate{int op,a,b;};
struct Stats{int fn=0,fp=0,boundary=0,nots=0;bool freeLive=false;int errors()const{return fn+fp;}};
struct Circ{std::array<Gate,G>gs;std::array<TT,N+G>w{};int out=0;Stats st;};
const std::array<std::pair<int,int>,15>edges={{{0,1},{1,2},{2,3},{3,4},{4,0},{0,5},{1,6},{2,7},{3,8},{4,9},{5,7},{7,9},{9,6},{6,8},{8,5}}};
std::array<TT,N>inputs;TT target{},boundary{},zero{};std::vector<int>covers;std::mt19937_64 rng(1884);int rnd(int n){assert(n>0);return rng()%n;}
bool goal(unsigned x){for(auto[a,b]:edges)if((x>>a&1)&&(x>>b&1))return true;return false;}
void setup(){for(unsigned x=0;x<1024;x++){U b=U(1)<<(x%64);for(int i=0;i<10;i++)if(x>>i&1)inputs[i][x/64]|=b;if(!(x&1))inputs[10][x/64]|=b;bool f=goal(x);if(f)target[x/64]|=b;bool mark=f&&std::popcount(x)==2;if(!f){mark=true;for(int i=0;i<10;i++)if(!(x>>i&1)&&!goal(x|(1u<<i)))mark=false;}if(mark)boundary[x/64]|=b;}
 for(unsigned c=0;c<1024;c++)if(std::popcount(c)==6){bool ok=true;for(auto[a,b]:edges)if(!(c>>a&1)&&!(c>>b&1))ok=false;if(ok)covers.push_back(c);}assert(!covers.empty());}
TT gateTruth(Gate g,const std::vector<TT>&w){TT v;for(int k=0;k<16;k++){U a=g.a<0?0:w[g.a][k],b=g.b<0?0:w[g.b][k];v[k]=g.op==0?(a&b):g.op==1?(a|b):g.op==2?~a:g.op==3?~U(0):0;}return v;}
void eval(Circ&c,int start=0){for(int j=start;j<G;j++){auto g=c.gs[j];for(int k=0;k<16;k++){U a=g.a<0?0:c.w[g.a][k],b=g.b<0?0:c.w[g.b][k];c.w[N+j][k]=g.op==0?(a&b):g.op==1?(a|b):g.op==2?~a:g.op==3?~U(0):0;}}
 c.st={};auto&w=c.out<0?zero:c.w[c.out];for(int k=0;k<16;k++){c.st.fn+=std::popcount(target[k]&~w[k]);c.st.fp+=std::popcount(~target[k]&w[k]);c.st.boundary+=std::popcount((w[k]^target[k])&boundary[k]);}
 bool live[N+G]{};if(c.out>=0)live[c.out]=true;for(int j=G-1;j>=0;j--){auto g=c.gs[j];c.st.nots+=g.op==2;if(live[N+j]){if(g.op<=2&&g.a>=0)live[g.a]=true;if(g.op<=1&&g.b>=0)live[g.b]=true;}}c.st.freeLive=live[10];}
std::pair<std::vector<Gate>,int>control(int distributed=0,bool useFree=false){
 int cover=covers[rnd(covers.size())];std::vector<int>ns[10],order;for(auto[a,b]:edges){if(!(cover>>a&1)||((cover>>b&1)&&rnd(2)))std::swap(a,b);ns[a].push_back(b);}for(int a=0;a<10;a++)if(!ns[a].empty())order.push_back(a);assert(order.size()==6);std::shuffle(order.begin(),order.end(),rng);
 std::vector<Gate>gs;int coeff[10];for(int a:order){std::shuffle(ns[a].begin(),ns[a].end(),rng);int v=ns[a][0];for(unsigned k=1;k<ns[a].size();k++){gs.push_back({1,v,ns[a][k]});v=N+gs.size()-1;}coeff[a]=v;}
 std::vector<int>terms;for(int i=distributed;i<6;i++){int a=order[i];gs.push_back({0,a,coeff[a]});terms.push_back(N+gs.size()-1);}while(terms.size()>1){int j=rnd(terms.size()),a=terms[j];terms.erase(terms.begin()+j);j=rnd(terms.size());int b=terms[j];terms.erase(terms.begin()+j);gs.push_back({1,a,b});terms.push_back(N+gs.size()-1);}int out=terms[0];
 for(int i=0;i<distributed;i++){int a=order[i];gs.push_back({1,a,out});int u=N+gs.size()-1;gs.push_back({1,coeff[a],out});int v=N+gs.size()-1;gs.push_back({0,u,v});out=N+gs.size()-1;}assert(gs.size()==20+distributed);
 if(useFree){auto ren=[](int x){return x==0?N:x>=N?x+1:x;};for(auto&g:gs){g.a=ren(g.a);g.b=ren(g.b);}out=ren(out);gs.insert(gs.begin(),{2,10,-1});}return {gs,out};}
bool verify(const std::vector<Gate>&gs,int out,const char*label){std::vector<TT>w(inputs.begin(),inputs.end());for(unsigned j=0;j<gs.size();j++){auto g=gs[j];assert(g.op>=0&&g.op<=4&&g.a<N+(int)j&&g.b<N+(int)j);w.push_back(gateTruth(g,w));}int bad=0;auto&v=out<0?zero:w[out];for(int k=0;k<16;k++)bad+=std::popcount(v[k]^target[k]);std::printf("CONTROL %s gates=%zu full_rows=1024 wrong=%d\n",label,gs.size(),bad);std::fflush(stdout);return bad==0;}
void reorder(std::vector<Gate>&gs,int&out){int count=gs.size();int map[N+MAXG];std::fill(map,map+N+MAXG,-2);for(int i=0;i<N;i++)map[i]=i;auto ready=[&](int x){return x<0||map[x]!=-2;};auto ren=[&](int x){return x<0?-1:map[x];};std::vector<int>todo;for(int i=0;i<count;i++)todo.push_back(i);std::vector<Gate>fresh;while(!todo.empty()){std::vector<int>cand;for(unsigned k=0;k<todo.size();k++){auto g=gs[todo[k]];if(g.op>=3||(ready(g.a)&&(g.op==2||ready(g.b))))cand.push_back(k);}int z=cand[rnd(cand.size())],j=todo[z];auto g=gs[j];map[N+j]=N+fresh.size();fresh.push_back({g.op,g.op>=3?-1:ren(g.a),g.op>=2?-1:ren(g.b)});todo.erase(todo.begin()+z);}out=ren(out);gs=std::move(fresh);}
Circ seed(){int z=rnd(100),d=z<60?0:z<90?1:2;auto[gs,out]=control(d,rnd(5)==0);while(gs.size()>G){int j=rnd(gs.size()),wire=N+j;auto g=gs[j];int sub=(g.op<=1&&rnd(2))?g.b:g.a;auto ren=[&](int x){if(x==wire)x=sub;return x>wire?x-1:x;};gs.erase(gs.begin()+j);for(auto&h:gs){h.a=ren(h.a);h.b=ren(h.b);}out=ren(out);}reorder(gs,out);Circ c;std::copy(inputs.begin(),inputs.end(),c.w.begin());std::copy(gs.begin(),gs.end(),c.gs.begin());c.out=out;if(rnd(4)==0)c.gs[rnd(G)].op=2;eval(c);return c;}
double score(const Stats&s,int lane){double v=lane==0?s.errors():lane==1?s.errors()+8*s.boundary:lane==2?4*s.fn+s.fp:s.fn+4*s.fp;v+=32*std::max(0,s.nots-1);return v;}
void save(const std::vector<Gate>&gs,int out,const std::string&path){std::ofstream f(path);f<<"{\"physical_inputs\":11,\"input_map\":[0,1,2,3,4,5,6,7,8,9],\"free_unary\":\"not\",\"gates\":[";for(unsigned j=0;j<gs.size();j++){auto g=gs[j];if(j)f<<',';f<<'['<<g.op<<','<<(g.a<0?100000:g.a)<<','<<(g.b<0?100000:g.b)<<']';}f<<"],\"output\":"<<(out<0?100000:out)<<"}\n";}
void save(const Circ&c,const std::string&path){save(std::vector<Gate>(c.gs.begin(),c.gs.end()),c.out,path);}
void print(const Circ&c,unsigned long long it,double sec,const char*kind){std::printf("%s seconds=%.3f iterations=%llu fn=%d fp=%d boundary=%d nots=%d free_live=%d output=%d\n",kind,sec,it,c.st.fn,c.st.fp,c.st.boundary,c.st.nots,c.st.freeLive,c.out);for(int j=0;j<G;j++){auto g=c.gs[j];std::printf("%d %d %d %d\n",N+j,g.op,g.a,g.b);}std::fflush(stdout);}
int main(int argc,char**argv){if(argc<3){std::fprintf(stderr,"usage: search SECONDS OUTPUT_PREFIX [RNG_SEED]\n");return 2;}int duration=std::atoi(argv[1]);std::string prefix=argv[2];if(argc>3)rng.seed(std::strtoull(argv[3],nullptr,10));setup();auto stop=std::filesystem::path(prefix).parent_path().parent_path()/"STOP";auto local=std::filesystem::path(prefix).parent_path()/"STOP";
 for(int d=0;d<3;d++){auto[gs,out]=control(d);if(!verify(gs,out,"monotone-distributive"))return 3;save(gs,out,prefix+".control"+std::to_string(d)+".json");}auto[freeGs,freeOut]=control(0,true);if(!verify(freeGs,freeOut,"free-not-live"))return 3;save(freeGs,freeOut,prefix+".control3.json");if(!duration)return 0;
 std::vector<Circ>pop;for(int i=0;i<128;i++)pop.push_back(seed());Circ best=pop[0];int bestErr=best.st.errors();auto start=std::chrono::steady_clock::now();unsigned long long it=0;double sec=0,next=60;bool stopped=false;print(best,0,0,"INITIAL");
 for(;;it++){if(it%65536==0){sec=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();if(std::filesystem::exists(stop)||std::filesystem::exists(local)){stopped=true;break;}if(sec>=duration)break;if(sec>=next){print(best,it,sec,"STATUS");next+=60;}}
  int slot=rnd(pop.size()),lane=slot%4;Circ c=pop[slot];int lo=G;if(rnd(1500)==0){std::vector<Gate>gs(c.gs.begin(),c.gs.end());int out=c.out;reorder(gs,out);std::copy(gs.begin(),gs.end(),c.gs.begin());c.out=out;lo=0;}else{int changes=1+(rnd(100)<20)+(rnd(100)<3?rnd(5):0);for(int k=0;k<changes;k++){int j=rnd(G),mode=rnd(10);lo=std::min(lo,j);if(mode<2){int z=rnd(100);c.gs[j].op=z<45?0:z<90?1:z<98?2:z==98?3:4;}else if(mode<5)c.gs[j].a=rnd(N+j+1)-1;else if(mode<8)c.gs[j].b=rnd(N+j+1)-1;else c.gs[j]=pop[rnd(pop.size())].gs[j];}if(rnd(100)<1)c.out=rnd(N+G);}
  eval(c,lo);double before=score(pop[slot].st,lane),after=score(c.st,lane);if(slot%8<4){before+=pop[slot].st.freeLive?0:8;after+=c.st.freeLive?0:8;}double temp=(slot/4)%8==0?2.0:(slot/4)%8==1?0.5:(slot/4)%8==2?0.1:0;if(after<=before||(temp&&double(rng())/double(UINT64_MAX)<std::exp((before-after)/temp)))pop[slot]=c;
  if(c.st.errors()<bestErr){bestErr=c.st.errors();best=c;print(c,it,sec,"BEST");save(c,prefix+".best.json");}if(!c.st.errors()){std::vector<Gate>gs(c.gs.begin(),c.gs.end());if(!verify(gs,c.out,"candidate"))return 3;save(c,prefix+".counterexample.json");std::puts("COUNTEREXAMPLE_REQUIRES_INDEPENDENT_VALIDATION");return 10;}
  if(it%131072==0)pop[rnd(pop.size())]=seed();if(it%262144==0)pop[rnd(pop.size())]=best;
 }print(best,it,sec,"FINAL");save(best,prefix+".final.json");std::printf("%s no_counterexample seconds=%.3f iterations=%llu\n",stopped?"STOPPED":"DONE",sec,it);return stopped?75:0;}
