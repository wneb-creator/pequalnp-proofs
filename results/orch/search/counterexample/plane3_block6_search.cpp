#include <array>
#include <vector>
#include <random>
#include <fstream>
#include <iostream>
#include <chrono>
#include <cmath>
#include <algorithm>
using TT=__uint128_t;
struct Gate {int op,a,b;};
static std::mt19937_64 rng(2583001);
static const int E[24][2]={{0,11},{0,16},{1,11},{1,12},{2,12},{2,13},{3,11},{3,13},{3,14},{4,12},{4,14},{5,13},{5,15},{6,14},{6,16},{7,11},{7,15},{8,12},{8,15},{8,16},{9,13},{9,16},{10,14},{10,15}};
static const int samples[76]={2049,65537,2050,4098,4100,8196,2056,8200,16392,4112,16400,8224,32800,16448,65600,2176,32896,4352,33024,65792,8704,66048,17408,33792,2047,3956,5865,7776,9683,11600,13505,15424,17319,19236,21153,23072,24963,26880,28801,33375,35412,37449,39488,41043,43088,45121,47168,49671,51716,53761,55808,57347,61441,66750,68660,70824,72736,74898,76816,78976,80896,82086,84004,86176,88096,90242,94336,98334,100372,102408,106514,108560,114694,116740,122882,129024};
std::array<TT,80> w;
TT target=0;
int score(const std::vector<Gate>& g){
 int penalty=0;
 for(int i=0;i<(int)g.size();i++){
  TT a=w[g[i].a],b=w[g[i].b];
  w[17+i]=g[i].op?(a|b):(a&b);
  if(!(a&~b)||!(b&~a))penalty+=4;
  if((w[17+i]&((TT(1)<<24)-1))==0)penalty+=4;
 }
 TT error=w[16+g.size()]^target;
 int score=__builtin_popcountll((unsigned long long)error)+__builtin_popcountll((unsigned long long)(error>>64));
 if(score==0)return 0;
 return score+penalty;
}

std::vector<Gate> seed(int n){
 std::vector<int> vs{11,12,13,14,15,16};
 std::shuffle(vs.begin(),vs.end(),rng);
 std::vector<Gate> g;std::vector<int> stars;
 bool covered[24]={};
 for(auto v:vs){std::vector<int> ns;for(int e=0;e<24;e++)if(!covered[e]&&(E[e][0]==v||E[e][1]==v)){covered[e]=true;ns.push_back(E[e][0]^E[e][1]^v);}if(ns.empty())continue;
  std::shuffle(ns.begin(),ns.end(),rng);int root=ns[0];for(int i=1;i<(int)ns.size();i++){g.push_back({1,root,ns[i]});root=16+g.size();}g.push_back({0,v,root});stars.push_back(16+g.size());
 }
 int root=stars[0];for(int i=1;i<(int)stars.size();i++){g.push_back({1,root,stars[i]});root=16+g.size();}
 while((int)g.size()>n){int d=rng()%g.size(),replacement=(rng()%2?g[d].a:g[d].b);g.erase(g.begin()+d);for(auto&z:g){if(z.a==17+d)z.a=replacement;else if(z.a>17+d)z.a--;if(z.b==17+d)z.b=replacement;else if(z.b>17+d)z.b--;}}
 return g;
}
void dump(const std::vector<Gate>&g,int s,unsigned long long it,const char*path){std::ofstream f(path);f<<"score "<<s<<" iterations "<<it<<"\n";for(auto z:g)f<<z.op<<" "<<z.a<<" "<<z.b<<"\n";}
int main(int argc,char**argv){int n=argc>1?std::stoi(argv[1]):28,secs=argc>2?std::stoi(argv[2]):1200;unsigned long long calls=0;
 if(argc>3)rng.seed(std::stoull(argv[3]));
 for(int j=0;j<76;j++){int x=samples[j];for(int i=0;i<17;i++)if((x>>i)&1)w[i]|=TT(1)<<j;bool t=false;for(auto&e:E)t|=((x>>e[0])&1)&&((x>>e[1])&1);if(t)target|=TT(1)<<j;}
 auto start=std::chrono::steady_clock::now();int best=100000;std::vector<Gate> bestg;std::vector<std::vector<Gate>> pool;
 for(int run=0;;run++){
  auto g=seed(n);int s=score(g);
  if(run%3!=0&&pool.size()){g=pool[rng()%pool.size()];for(int k=0;k<1+run%6;k++){int i=rng()%n;g[i]={(int)(rng()%2),(int)(rng()%(17+i)),(int)(rng()%(17+i))};}s=score(g);}
  for(int it=0;it<100000;it++){
   int i=rng()%n,type=rng()%4;auto old=g[i];if(type==0)g[i].op=1-g[i].op;else if(type==1)g[i].a=rng()%(17+i);else if(type==2)g[i].b=rng()%(17+i);else g[i]={(int)(rng()%2),(int)(rng()%(17+i)),(int)(rng()%(17+i))};
   if(g[i].a==g[i].b){g[i]=old;continue;}
   int ns=score(g);calls++;double temp=0.02+1.2*(1.0-(it%10000)/10000.0);
   if(ns<=s||std::generate_canonical<double,53>(rng)<std::exp((s-ns)/temp))s=ns;else g[i]=old;
   if(s<best){best=s;bestg=g;dump(g,s,calls,"/tmp/oec/pequalnp-pilot-131/plane3-block6-best.txt");std::cout<<"best "<<best<<" calls "<<calls<<" run "<<run<<std::endl;if(s==0)return 0;}
   if(s==best&&it%1000==0){if(pool.size()<100)pool.push_back(g);else pool[rng()%100]=g;}
   if(calls%1000000==0&&std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()>secs){std::cout<<"DONE calls "<<calls<<" best "<<best<<std::endl;return 1;}
  }
 }
}
