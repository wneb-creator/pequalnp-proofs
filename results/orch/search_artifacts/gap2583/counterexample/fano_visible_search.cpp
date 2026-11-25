#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <random>
#include <vector>
using U=uint64_t;
struct Gate{int op,a,b;};
struct Circ{std::array<Gate,26>gs;std::array<U,40>w;int score;};
std::mt19937_64 rng(2584);int rnd(int n){return rng()%n;}
std::vector<std::pair<int,int>>edges;std::vector<int>adj[14],rows;U inp[14]={},target=0;
bool function(int r){for(auto[a,b]:edges)if((r>>a&1)&&(r>>b&1))return true;return false;}
int eval(Circ&c,int start=0){for(int i=start;i<26;i++){auto g=c.gs[i];c.w[14+i]=g.op?(c.w[g.a]|c.w[g.b]):(c.w[g.a]&c.w[g.b]);}U wrong=c.w[39]^target; int invisible=0,nand=0; for(int i=0;i<26;i++){invisible+=!(c.w[14+i]&target);nand+=!c.gs[i].op;} return c.score=std::popcount(wrong&target)*8+std::popcount(wrong&~target)+invisible+2*std::max(0,8-nand);}
Circ seed(){
 std::vector<Gate>gs;std::vector<int>order,terms;int side=rnd(2);
 for(int i=0;i<7;i++)order.push_back(i+7*side);std::shuffle(order.begin(),order.end(),rng);
 for(int v:order){auto ns=adj[v];std::shuffle(ns.begin(),ns.end(),rng);gs.push_back({1,ns[0],ns[1]});int u=13+gs.size();gs.push_back({1,u,ns[2]});u=13+gs.size();gs.push_back({0,v,u});terms.push_back(13+gs.size());}
 while(terms.size()>1){int i=rnd(terms.size()),a=terms[i];terms.erase(terms.begin()+i);i=rnd(terms.size());int b=terms[i];terms.erase(terms.begin()+i);gs.push_back({1,a,b});terms.push_back(13+gs.size());}
 int del=rnd(26),sub=rnd(2)?gs[del].a:gs[del].b;gs.erase(gs.begin()+del);
 auto tr=[&](int x){if(x==14+del)x=sub;return x>14+del?x-1:x;};
 Circ c;for(int i=0;i<14;i++)c.w[i]=inp[i];for(int i=0;i<26;i++)c.gs[i]={gs[i].op,tr(gs[i].a),tr(gs[i].b)};eval(c);return c;
}
void print(const Circ&c,unsigned long long it,double seconds){std::printf("BEST score=%d errors=%d iterations=%llu seconds=%.1f\n",c.score,std::popcount(c.w[39]^target),it,seconds);for(int i=0;i<26;i++){auto g=c.gs[i];std::printf("%d %c %d %d\n",14+i,"&|"[g.op],g.a,g.b);}std::fflush(stdout);}
int main(int argc,char**argv){
 int duration=argc>1?std::atoi(argv[1]):600;
 for(int l=0;l<7;l++)for(int d:{0,1,3}){int p=(l+d)%7;edges.push_back({p,7+l});adj[p].push_back(7+l);adj[7+l].push_back(p);rows.push_back((1<<p)|(1<<(7+l)));}
 for(int r=0;r<(1<<14);r++)if(!function(r)){bool maximal=true;for(int i=0;i<14;i++)if(!(r>>i&1)&&!function(r|(1<<i)))maximal=false;if(maximal)rows.push_back(r);}
 std::sort(rows.begin(),rows.end());std::printf("ROWS %zu\n",rows.size());if(rows.size()!=58)return 2;
 for(int r=0;r<(int)rows.size();r++){for(int i=0;i<14;i++)if(rows[r]>>i&1)inp[i]|=U(1)<<r;if(function(rows[r]))target|=U(1)<<r;}
 auto t=std::chrono::steady_clock::now();std::vector<Circ>pop;for(int i=0;i<256;i++)pop.push_back(seed());Circ best=pop[0];double seconds=0;unsigned long long it=0;print(best,0,0);
 for(;;it++){
  if(it%262144==0){seconds=std::chrono::duration<double>(std::chrono::steady_clock::now()-t).count();if(seconds>=duration)break;}
  int slot=rnd(256);Circ old=pop[slot],c=old;int lo=26;int changes=1+(rnd(100)<20)+(rnd(100)<5?rnd(6):0);
  for(int z=0;z<changes;z++){int j=rnd(26);lo=std::min(lo,j);int mode=rnd(6);if(mode==0)c.gs[j].op^=1;else if(mode<3)c.gs[j].a=rnd(14+j);else if(mode<5)c.gs[j].b=rnd(14+j);else c.gs[j]=pop[rnd(256)].gs[j];}
  eval(c,lo);double temp=slot%8==0?2.0:slot%8==1?0.8:slot%8==2?0.2:0;
  if(c.score<=old.score||(temp>0&&double(rng())/double(UINT64_MAX)<std::exp((old.score-c.score)/temp)))pop[slot]=c;
  if(c.w[39]==target){print(c,it,seconds);std::puts("VERIFIED ROW WITNESS");return 0;} if(c.score<best.score){best=c;print(c,it,seconds);}
  if(it%65536==0)pop[rnd(256)]=seed();if(it%1048576==0)pop[rnd(256)]=best;
 }
 print(best,it,seconds);
}
