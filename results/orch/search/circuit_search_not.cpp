#include <array>
#include <vector>
#include <random>
#include <fstream>
#include <iostream>
#include <chrono>
#include <cmath>
#include <algorithm>
using TT=std::array<unsigned long long,16>;
struct Gate {int op,a,b;};
static std::mt19937_64 rng(232592);
static const int E[15][2]={{0,1},{1,2},{2,3},{3,4},{4,0},{0,5},{1,6},{2,7},{3,8},{4,9},{5,7},{7,9},{9,6},{6,8},{8,5}};
std::array<TT,30> w;
TT target;
int score(const std::vector<Gate>& g,int fpweight){
 for(int i=0;i<(int)g.size();i++)for(int k=0;k<16;k++){
  auto a=w[g[i].a][k], b=w[g[i].b][k];
  w[10+i][k]=g[i].op==0?(a&b):g[i].op==1?(a|b):~a;
 }
 int s=0;for(int k=0;k<16;k++)s+=fpweight*__builtin_popcountll(w[9+g.size()][k]&~target[k])+__builtin_popcountll(~w[9+g.size()][k]&target[k]);
 int nnot=0;for(auto z:g)nnot+=(z.op==2);return s+(nnot==0?32:0);
}
std::vector<Gate> seed(int n){
 std::vector<int> vs{1,3,4,5,6,7};
 std::shuffle(vs.begin(),vs.end(),rng);
 std::vector<Gate> g;std::vector<int> stars;
 bool covered[15]={};
 for(auto v:vs){std::vector<int> ns;for(int e=0;e<15;e++)if(!covered[e]&&(E[e][0]==v||E[e][1]==v)){covered[e]=true;ns.push_back(E[e][0]^E[e][1]^v);}if(ns.empty())continue;
  int root=ns[0];for(int i=1;i<(int)ns.size();i++){g.push_back({1,root,ns[i]});root=9+g.size();}g.push_back({0,v,root});stars.push_back(9+g.size());
 }
 int root=stars[0];for(int i=1;i<(int)stars.size();i++){g.push_back({1,root,stars[i]});root=9+g.size();}
 while((int)g.size()>n){int d=rng()%g.size(),replacement=(rng()%2?g[d].a:g[d].b);g.erase(g.begin()+d);for(auto& z:g){if(z.a==10+d)z.a=replacement;else if(z.a>10+d)z.a--;if(z.b==10+d)z.b=replacement;else if(z.b>10+d)z.b--;}}
 return g;
}
void dump(const std::vector<Gate>& g,int s,unsigned long long it,const char *path){std::ofstream f(path);f<<"score "<<s<<" iterations "<<it<<"\n";for(auto z:g)f<<z.op<<" "<<z.a<<" "<<z.b<<"\n";}
int main(int argc,char**argv){int n=argc>1?std::stoi(argv[1]):19,secs=argc>2?std::stoi(argv[2]):600,fpw=argc>3?std::stoi(argv[3]):10;unsigned long long calls=0;
 for(int x=0;x<1024;x++){for(int i=0;i<10;i++)if((x>>i)&1)w[i][x/64]|=1ULL<<(x%64);bool t=false;for(auto&e:E)t|=((x>>e[0])&1)&&((x>>e[1])&1);if(t)target[x/64]|=1ULL<<(x%64);}
 auto start=std::chrono::steady_clock::now();int best=100000;std::vector<Gate> bestg;
 for(int run=0;;run++){
  auto g=seed(n);int s=score(g,fpw);
  if(run%4!=0&&bestg.size()){g=bestg;for(int k=0;k<1+run%6;k++){int i=rng()%n;g[i]={(int)(rng()%10==0?2:rng()%2),(int)(rng()%(10+i)),(int)(rng()%(10+i))};}s=score(g,fpw);}
  for(int it=0;it<200000;it++){
   int i=rng()%n,type=rng()%4;auto old=g[i];if(type==0)g[i].op=rng()%3;else if(type==1)g[i].a=rng()%(10+i);else if(type==2)g[i].b=rng()%(10+i);else g[i]={(int)(rng()%10==0?2:rng()%2),(int)(rng()%(10+i)),(int)(rng()%(10+i))};
   int ns=score(g,fpw);calls++;double temp=0.15+4.0*(1.0-(it%50000)/50000.0);
   if(ns<=s||std::generate_canonical<double,53>(rng)<std::exp((s-ns)/temp))s=ns;else g[i]=old;
   if(s<best){best=s;bestg=g;dump(g,s,calls,"/tmp/oec/pequalnp-pilot-131/search-not-best.txt");std::cout<<"best "<<best<<" calls "<<calls<<" run "<<run<<std::endl;if(s==0)return 0;}
   if(calls%100000==0&&std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()>secs){std::cout<<"DONE calls "<<calls<<" best "<<best<<std::endl;return 1;}
  }
 }
}
