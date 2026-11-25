#include <algorithm>
#include <array>
#include <cassert>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <random>
#include <vector>
using U=uint64_t;
constexpr int P=8,N=16;
struct Gate{int a,b,op;};using Circuit=std::vector<Gate>;
std::mt19937_64 rng(86);int rnd(int n){return rng()%n;}
std::array<U,4> evaluate(const Circuit&gs,const std::vector<int>&tests){
 U vals[64][4]{};int words=(tests.size()+63)/64;
 for(int a=0;a<int(tests.size());a++)for(int i=0;i<N;i++)if(tests[a]>>i&1)vals[i][a/64]|=U(1)<<(a%64);
 for(int i=0;i<int(gs.size());i++)for(int w=0;w<words;w++)vals[N+i][w]=gs[i].op?(vals[gs[i].a][w]|vals[gs[i].b][w]):(vals[gs[i].a][w]&vals[gs[i].b][w]);
 std::array<U,4>out{};for(int w=0;w<words;w++)out[w]=vals[N+gs.size()-1][w];return out;
}
int live(const Circuit&gs){std::array<bool,64>seen{};std::vector<int>q{N+int(gs.size())-1};int count=0;
 while(!q.empty()){int i=q.back();q.pop_back();if(i<N||seen[i])continue;seen[i]=true;count++;q.push_back(gs[i-N].a);q.push_back(gs[i-N].b);}return count;}
int matching(const std::array<int,P>&rows){int mt[P];std::fill(mt,mt+P,-1);int result=0;
 auto dfs=[&](auto&&self,int v,int&seen)->bool{for(int u=0;u<P;u++)if((rows[v]>>u&1)&&!(seen>>u&1)){seen|=1<<u;if(mt[u]<0||self(self,mt[u],seen)){mt[u]=v;return true;}}return false;};
 for(int v=0;v<P;v++){int seen=0;result+=dfs(dfs,v,seen);}return result;}
struct Result{double fitness;U graph;int gap,errors,c4,used;};
std::vector<int>pairtests;
Result assess(const Circuit&gs){auto f=evaluate(gs,pairtests);U graph=f[0];int pure=__builtin_popcountll(f[1]);std::array<int,P>rows{};for(int p=0;p<P;p++)rows[p]=(graph>>(P*p))&255;
 int edgecount=__builtin_popcountll(graph);if(edgecount<20)return {-100.0+edgecount,graph,-100,0,0,0};
 int c4=0;for(int p=0;p<P;p++)for(int q=0;q<p;q++){int t=__builtin_popcount(unsigned(rows[p]&rows[q]));c4+=t*(t-1)/2;}
 if(pure||c4)return {-20.0*pure-5.0*c4,graph,-100,pure,c4,0};
 std::vector<int>negative;
 for(int points=0;points<(1<<P);points++){int forbidden=0;for(int p=0;p<P;p++)if(points>>p&1)forbidden|=rows[p];int lines=255^forbidden;int closure=0;for(int p=0;p<P;p++)if(!(rows[p]&lines))closure|=1<<p;if(closure==points)negative.push_back(points|(lines<<P));}
 assert(negative.size()<=256);auto bad=evaluate(gs,negative);int errors=0;for(U x:bad)errors+=__builtin_popcountll(x);
 int used=live(gs),gap=edgecount+matching(rows)-1-used;
 return {gap-4.0*errors+0.2*edgecount,graph,gap,errors,0,used};}
Circuit baseline(){Circuit gs;std::vector<int>centres(P),roots;for(int i=0;i<P;i++)centres[i]=i;std::shuffle(centres.begin(),centres.end(),rng);
 auto add=[&](int a,int b,int op){gs.push_back({a,b,op});return N+int(gs.size())-1;};
 for(int dead=0;dead<9;dead++)add(rnd(N),rnd(N),rnd(2));
 for(int p:centres){std::vector<int>ls{P+p,P+(p+1)%P,P+(p+3)%P};std::shuffle(ls.begin(),ls.end(),rng);int rt=add(ls[0],ls[1],1);rt=add(rt,ls[2],1);roots.push_back(add(p,rt,0));}
 std::shuffle(roots.begin(),roots.end(),rng);int rt=roots[0];for(size_t i=1;i<roots.size();i++)rt=add(rt,roots[i],1);return gs;}
void report(const Circuit&gs,const Result&r){
 for(int x=0;x<(1<<N);x++){bool ws[64]{};for(int i=0;i<N;i++)ws[i]=x>>i&1;for(int i=0;i<int(gs.size());i++)ws[N+i]=gs[i].op?(ws[gs[i].a]||ws[gs[i].b]):(ws[gs[i].a]&&ws[gs[i].b]);bool target=false;for(int p=0;p<P;p++)for(int l=0;l<P;l++)if((r.graph>>(P*p+l)&1)&&(x>>p&1)&&(x>>(P+l)&1))target=true;assert(ws[N+gs.size()-1]==target);}
 std::cout<<"FOUND graph "<<r.graph<<" live gates "<<r.used<<" saving "<<r.gap<<" full truth table verified\n";for(auto g:gs)std::cout<<g.a<<" "<<g.b<<" "<<g.op<<"\n";
}
int main(int argc,char**argv){int seconds=std::atoi(argv[1]);if(argc>2)rng.seed(std::strtoull(argv[2],nullptr,10));for(int p=0;p<P;p++)for(int l=0;l<P;l++)pairtests.push_back((1<<p)|(1<<(P+l)));pairtests.push_back(255);pairtests.push_back(255<<P);
 auto start=std::chrono::steady_clock::now();long long trials=0,valid=0,validEdges=0;int restarts=0,best=-100;
 std::cout<<"Dynamic8x8 graph search,40gate genome with9initially dead gates, at least20edges; exact monotone antichain tests\n"<<std::flush;
 while(std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<seconds){++restarts;Circuit c=baseline();auto cur=assess(c);assert(cur.gap==0&&cur.errors==0&&cur.c4==0);
 for(int it=0;it<100000;it++){Circuit d=c;int changes=rnd(100)<10?2:1;for(int k=0;k<changes;k++){int j=rnd(d.size()),kind=rnd(3);if(kind==0)d[j].a=rnd(N+j);else if(kind==1)d[j].b=rnd(N+j);else d[j].op^=1;}auto s=assess(d);++trials;if(s.c4==0&&s.errors==0&&s.gap>-100){++valid;validEdges+=__builtin_popcountll(s.graph);if(s.gap>best){best=s.gap;std::cout<<"best saving "<<best<<" at "<<trials<<" trials; valid "<<valid<<std::endl;}if(s.gap>0){report(d,s);return 2;}}
 double temp=0.8*(1.0-double(it)/100000)+0.05;if(s.fitness>=cur.fitness||double(rng()%1000000)/1000000.0<std::exp((s.fitness-cur.fitness)/temp)){c=std::move(d);cur=s;}}
 }
 std::cout<<"Completed no witness; trials "<<trials<<" valid "<<valid<<" restarts "<<restarts<<" best saving "<<best<<" mean valid edges "<<(valid?double(validEdges)/valid:0)<<std::endl;
}
