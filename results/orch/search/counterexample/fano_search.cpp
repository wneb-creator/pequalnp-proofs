#include <array>
#include <vector>
#include <random>
#include <fstream>
#include <iostream>
#include <chrono>
#include <cmath>
#include <algorithm>
using TT=unsigned long long;
struct Gate {int op,a,b;};
static std::mt19937_64 rng(2583001);
static const int E[21][2]={{0,7},{0,11},{0,13},{1,7},{1,8},{1,12},{2,8},{2,9},{2,13},{3,7},{3,9},{3,10},{4,8},{4,10},{4,11},{5,9},{5,11},{5,12},{6,10},{6,12},{6,13}};
static const int samples[58]={129,2049,8193,130,258,4098,260,516,8196,136,520,1032,272,1040,2064,544,2080,4128,1088,4160,8256,127,244,361,480,595,720,833,1063,1188,1313,1539,2126,2244,2376,2626,3008,3078,4125,4244,4361,4625,5125,5889,6156,7300,8250,8368,8488,8722,9250,9632,10250,11778,12312,12944,14600,16256};
std::array<TT,80> w;
TT target=0;
int score(const std::vector<Gate>& g){
 for(int i=0;i<(int)g.size();i++)w[14+i]=g[i].op?(w[g[i].a]|w[g[i].b]):(w[g[i].a]&w[g[i].b]);
 return __builtin_popcountll(w[13+g.size()]^target);
}
std::vector<Gate> seed(int n){
 std::vector<int> vs;int side=rng()%2;for(int i=0;i<7;i++)vs.push_back(i+7*side);
 std::shuffle(vs.begin(),vs.end(),rng);
 std::vector<Gate> g;std::vector<int> stars;
 bool covered[21]={};
 for(auto v:vs){std::vector<int> ns;for(int e=0;e<21;e++)if(!covered[e]&&(E[e][0]==v||E[e][1]==v)){covered[e]=true;ns.push_back(E[e][0]^E[e][1]^v);}if(ns.empty())continue;
  std::shuffle(ns.begin(),ns.end(),rng);int root=ns[0];for(int i=1;i<(int)ns.size();i++){g.push_back({1,root,ns[i]});root=13+g.size();}g.push_back({0,v,root});stars.push_back(13+g.size());
 }
 int root=stars[0];for(int i=1;i<(int)stars.size();i++){g.push_back({1,root,stars[i]});root=13+g.size();}
 while((int)g.size()>n){int d=rng()%g.size(),replacement=(rng()%2?g[d].a:g[d].b);g.erase(g.begin()+d);for(auto&z:g){if(z.a==14+d)z.a=replacement;else if(z.a>14+d)z.a--;if(z.b==14+d)z.b=replacement;else if(z.b>14+d)z.b--;}}
 return g;
}
void dump(const std::vector<Gate>&g,int s,unsigned long long it,const char*path){std::ofstream f(path);f<<"score "<<s<<" iterations "<<it<<"\n";for(auto z:g)f<<z.op<<" "<<z.a<<" "<<z.b<<"\n";}
int main(int argc,char**argv){int n=argc>1?std::stoi(argv[1]):26,secs=argc>2?std::stoi(argv[2]):1200;unsigned long long calls=0;
 if(argc>3)rng.seed(std::stoull(argv[3]));
 for(int j=0;j<58;j++){int x=samples[j];for(int i=0;i<14;i++)if((x>>i)&1)w[i]|=1ULL<<j;bool t=false;for(auto&e:E)t|=((x>>e[0])&1)&&((x>>e[1])&1);if(t)target|=1ULL<<j;}
 auto start=std::chrono::steady_clock::now();int best=100000;std::vector<Gate> bestg;std::vector<std::vector<Gate>> pool;
 for(int run=0;;run++){
  auto g=seed(n);int s=score(g);
  if(run%3!=0&&pool.size()){g=pool[rng()%pool.size()];for(int k=0;k<1+run%6;k++){int i=rng()%n;g[i]={(int)(rng()%2),(int)(rng()%(14+i)),(int)(rng()%(14+i))};}s=score(g);}
  for(int it=0;it<100000;it++){
   int i=rng()%n,type=rng()%4;auto old=g[i];if(type==0)g[i].op=1-g[i].op;else if(type==1)g[i].a=rng()%(14+i);else if(type==2)g[i].b=rng()%(14+i);else g[i]={(int)(rng()%2),(int)(rng()%(14+i)),(int)(rng()%(14+i))};
   int ns=score(g);calls++;double temp=0.02+0.8*(1.0-(it%10000)/10000.0);
   if(ns<=s||std::generate_canonical<double,53>(rng)<std::exp((s-ns)/temp))s=ns;else g[i]=old;
   if(s<best){best=s;bestg=g;dump(g,s,calls,"/tmp/oec/pequalnp-pilot-131/fano-search-best.txt");std::cout<<"best "<<best<<" calls "<<calls<<" run "<<run<<std::endl;if(s==0)return 0;}
   if(s==best&&it%1000==0){if(pool.size()<100)pool.push_back(g);else pool[rng()%100]=g;}
   if(calls%1000000==0&&std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()>secs){std::cout<<"DONE calls "<<calls<<" best "<<best<<std::endl;return 1;}
  }
 }
}
