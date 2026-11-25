#include <array>
#include <vector>
#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <random>
#include <cmath>
#include <chrono>
#include <cstdlib>
using namespace std;
using TT=array<uint64_t,16>;
struct Gate{int op,a,b;};
struct Circuit{vector<Gate> g;};
mt19937_64 rng(2592);
TT inp[10],target,mask2,mask3,mask4;
vector<pair<int,int>> edges;
int rr(int n){return rng()%n;}
int pop(const TT &a){int s=0;for(auto v:a)s+=__builtin_popcountll(v);return s;}
int eval(const Circuit &c,int weighted=0){
 TT w[32];copy(inp,inp+10,w);int nots=0;
 for(int i=0;i<(int)c.g.size();i++){
  auto [op,a,b]=c.g[i];nots+=op==2;
  for(int j=0;j<16;j++)w[10+i][j]=op==0?(w[a][j]&w[b][j]):op==1?(w[a][j]|w[b][j]):~w[a][j];
 }
 TT diff;int score=0;
 for(int j=0;j<16;j++){
  uint64_t d=w[9+c.g.size()][j]^target[j];
  score+=__builtin_popcountll(d);
  if(weighted){score+=4*__builtin_popcountll(d&mask2[j])+2*__builtin_popcountll(d&mask3[j]);}
 }
 return score+(nots==0?1000:0);
}
Circuit initial(){
 array<array<int,4>,5> is={{{0,2,8,9},{0,3,6,7},{1,3,5,9},{1,4,7,8},{2,4,5,6}}};
 bool chosen[10]={};for(auto v:is[rr(5)])chosen[v]=true;
 vector<int> nbr[10];
 for(auto [a,b]:edges){if(chosen[a]||(!chosen[b]&&rr(2)))swap(a,b);nbr[a].push_back(b);}
 vector<int> centers;for(int i=0;i<10;i++)if(nbr[i].size())centers.push_back(i);
 shuffle(centers.begin(),centers.end(),rng);Circuit c;vector<int> terms;
 for(int a:centers){auto ns=nbr[a];shuffle(ns.begin(),ns.end(),rng);int p=ns[0];for(int i=1;i<(int)ns.size();i++){c.g.push_back({1,p,ns[i]});p=9+c.g.size();}c.g.push_back({0,a,p});terms.push_back(9+c.g.size());}
 shuffle(terms.begin(),terms.end(),rng);int p=terms[0];for(int i=1;i<(int)terms.size();i++){c.g.push_back({1,p,terms[i]});p=9+c.g.size();}
 if(c.g.size()!=20||eval(c)!=1000){fprintf(stderr,"bad base %zu %d\n",c.g.size(),eval(c));exit(2);}
 // Remove one gate by replacing references with either parent.
 int i=rr(19),rep=rr(2)?c.g[i].a:c.g[i].b;c.g.erase(c.g.begin()+i);
 for(auto &g:c.g){if(g.a==10+i)g.a=rep;else if(g.a>10+i)--g.a;if(g.b==10+i)g.b=rep;else if(g.b>10+i)--g.b;}
 // A NOT can arise by mutating a redundant gate; don't force it here.
 return c;
}
void printc(const Circuit &c,int score){printf("score %d gates %zu\n",score,c.g.size());for(int i=0;i<(int)c.g.size();i++)printf("%d %s %d %d\n",10+i,c.g[i].op==0?"AND":c.g[i].op==1?"OR":"NOT",c.g[i].a,c.g[i].b);fflush(stdout);}
int main(int argc,char**argv){
 int seconds=argc>1?atoi(argv[1]):600;if(argc>2)rng.seed(atoll(argv[2]));
 for(int i=0;i<5;i++){edges.push_back({i,(i+1)%5});edges.push_back({i,i+5});}for(auto e:vector<pair<int,int>>{{5,7},{7,9},{9,6},{6,8},{8,5}})edges.push_back(e);
 for(int r=0;r<1024;r++){for(int i=0;i<10;i++)if(r>>i&1)inp[i][r/64]|=1ULL<<(r%64);bool t=false;for(auto [a,b]:edges)t|=(r>>a&1)&&(r>>b&1);if(t)target[r/64]|=1ULL<<(r%64);auto *m=__builtin_popcount((unsigned)r)==2?&mask2:__builtin_popcount((unsigned)r)==3?&mask3:&mask4;(*m)[r/64]|=1ULL<<(r%64);}
 int best=99999;long long attempts=0,restarts=0;auto start=chrono::steady_clock::now();
 while(chrono::duration<double>(chrono::steady_clock::now()-start).count()<seconds){
  Circuit c=initial();int weighted=rr(2),s=eval(c,weighted);double temp=rr(2)?0.0:0.5;
  for(int k=0;k<100000;k++){
   int i=rr(c.g.size()),t=rr(3);Gate old=c.g[i];if(t==0)c.g[i].a=rr(10+i);if(t==1)c.g[i].b=rr(10+i);if(t==2)c.g[i].op=rr(3);
   int ns=eval(c,weighted);attempts++;
   if(ns<=s||(temp>0&&(double)rng()/UINT64_MAX<exp((s-ns)/temp)))s=ns;else c.g[i]=old;
   if(s<best){best=s;printc(c,eval(c));printf("weighted %d objective %d attempts %lld restarts %lld\n",weighted,s,attempts,restarts);fflush(stdout);}
   if(s==0){printc(c,0);return 0;}
  }
  restarts++;
 }
 printf("DONE attempts %lld restarts %lld best_objective %d\n",attempts,restarts,best);return 1;
}
