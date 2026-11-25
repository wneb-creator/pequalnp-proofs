#include <array>
#include <vector>
#include <random>
#include <chrono>
#include <iostream>
#include <fstream>
#include <algorithm>
#include <cmath>
#include <cstdint>
#include <bit>
using namespace std;
#ifndef INPUTS
#define INPUTS 26
#endif
#ifndef WORDS
#define WORDS 12
#endif
#ifndef TARGET
#define TARGET 63
#endif
#ifndef ACTIVEGATES
#define ACTIVEGATES 128
#endif
#ifndef POINTS
#define POINTS 13
#endif
constexpr int N=INPUTS,G=ACTIVEGATES,W=WORDS;
struct Gate {int op,a,b;};
using Bits=array<uint64_t,W>;
struct Circuit {array<Gate,G> gates;int output;};
array<Bits,N> inputs;Bits wanted{};
vector<vector<Gate>> seeds;
mt19937_64 rng;
bool require_nontrivial_and=false;
bool require_nonlinear=false;
int ri(int n){return rng()%n;}
vector<int> cone(const Circuit& c,int output){
 array<bool,N+G> used{};used[output]=true;vector<int> result;
 for(int k=G-1;k>=0;k--)if(used[N+k]){result.push_back(k);used[c.gates[k].a]=used[c.gates[k].b]=true;}
 return result;
}
int evaluate(Circuit& c){
 array<Bits,N+G> v;copy(inputs.begin(),inputs.end(),v.begin());
 array<int,N+G> degree{};for(int i=POINTS;i<N;i++)degree[i]=1;
 for(int k=0;k<G;k++){
  auto g=c.gates[k];for(int j=0;j<W;j++)v[N+k][j]=g.op?(v[g.a][j]|v[g.b][j]):(v[g.a][j]&v[g.b][j]);
  degree[N+k]=g.op?max(degree[g.a],degree[g.b]):min(2,degree[g.a]+degree[g.b]);
  if(v[N+k]==v[g.a])degree[N+k]=min(degree[N+k],degree[g.a]);
  if(v[N+k]==v[g.b])degree[N+k]=min(degree[N+k],degree[g.b]);
 }
 int best=1000000,bestout=c.output;
 for(int k=N;k<N+G;k++)if(v[k]==wanted && (!require_nonlinear || degree[k]>=2) &&
   (!require_nontrivial_and || (c.gates[k-N].op==0 &&
    v[c.gates[k-N].a]!=wanted && v[c.gates[k-N].b]!=wanted))){
  int count=cone(c,k).size();if(count<best){best=count;bestout=k;}}
 if(best<1000000){c.output=bestout;return best;}
 int miss=0,wrong=0;
 for(int j=0;j<W;j++){miss+=popcount(wanted[j]&~v[c.output][j]);wrong+=popcount(~wanted[j]&v[c.output][j]);}
 return 1000000+10000*(miss*16+wrong)+cone(c,c.output).size();
}
Circuit seed(){
 auto s=seeds[ri(seeds.size())];Circuit c;c.output=N+s.size()-1;
 copy(s.begin(),s.end(),c.gates.begin());
 for(int k=s.size();k<G;k++)c.gates[k]={ri(2),ri(N+k),ri(N+k)};
 return c;
}
void dump(const Circuit& c,const string& path){
 auto selected=cone(c,c.output);reverse(selected.begin(),selected.end());array<int,N+G> ren;
 for(int k=0;k<N;k++)ren[k]=k;
 for(int k=0;k<(int)selected.size();k++)ren[N+selected[k]]=N+k;
 ofstream f(path);f<<"[\n";
 for(int k=0;k<(int)selected.size();k++){auto g=c.gates[selected[k]];f<<"  ["<<g.op<<","<<ren[g.a]<<","<<ren[g.b]<<"]"<<(k+1<(int)selected.size()?",":"")<<"\n";}f<<"]\n";
}
int main(int argc,char**argv){
 if(argc!=6&&argc!=7){cerr<<"usage: search_active tests.txt seconds seed output-prefix seeds.txt [require-and|nonlinear]\n";return 2;}
 require_nonlinear=argc==7&&string(argv[6])=="nonlinear";
 require_nontrivial_and=argc==7&&!require_nonlinear;
 ifstream f(argv[1]);int m;f>>m;
 if(m>64*W){cerr<<"Too many tests for bit-vector width\n";return 3;}
 for(int j=0;j<m;j++){uint32_t x;int y;f>>x>>y;for(int i=0;i<N;i++)if((x>>i)&1)inputs[i][j/64]|=uint64_t(1)<<(j%64);if(y)wanted[j/64]|=uint64_t(1)<<(j%64);}
 ifstream s(argv[5]);int n;s>>n;while(n--){int k;s>>k;vector<Gate> c(k);for(auto& g:c)s>>g.op>>g.a>>g.b;seeds.push_back(c);}
 int duration=stoi(argv[2]);rng.seed(stoull(argv[3]));string prefix=argv[4];
 auto begin=chrono::steady_clock::now();long long it=0,restarts=0;int best=100000,lastreport=-1;
 Circuit current=seed();int score=evaluate(current);auto active=cone(current,current.output);
 while(true){
  double elapsed=chrono::duration<double>(chrono::steady_clock::now()-begin).count();if(elapsed>duration)break;
  if((int)elapsed/10>lastreport){lastreport=(int)elapsed/10;cout<<"seconds "<<elapsed<<" iterations "<<it<<" restarts "<<restarts<<" best "<<best<<" current "<<score<<endl;}
  Circuit next=current;int mutations=1+(ri(5)==0)+(ri(20)==0);
  for(int k=0;k<mutations;k++){
   int j=(ri(2)&&!active.empty())?active[ri(active.size())]:ri(G);int mode=ri(12);
   if(mode<5)next.gates[j].a=ri(N+j);else if(mode<10)next.gates[j].b=ri(N+j);else next.gates[j].op^=1;
  }
  int ns=evaluate(next);
  if(ns<best){best=ns;dump(next,prefix+"-best.json");cout<<"BEST "<<best<<" at "<<elapsed<<endl;}
  if(ns<=TARGET){dump(next,prefix+"-solution.json");cout<<"SOLUTION "<<prefix<<"-solution.json"<<endl;return 0;}
  double temp=((it/100000)%3==0)?0.1:(((it/100000)%3==1)?0.7:2.0);
  if(ns<=score || uniform_real_distribution<double>(0,1)(rng)<exp((score-ns)/temp)){current=next;score=ns;active=cone(current,current.output);}
  ++it;
  if(it%1000000==0){current=seed();score=evaluate(current);active=cone(current,current.output);restarts++;}
 }
 cout<<"DONE iterations "<<it<<" best "<<best<<endl;
}
