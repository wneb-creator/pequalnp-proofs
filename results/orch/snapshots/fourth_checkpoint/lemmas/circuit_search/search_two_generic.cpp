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
#include <bitset>
#include <cassert>
using namespace std;
#ifndef INPUTS
#define INPUTS 17
#endif
#ifndef GENOME_GATES
#define GENOME_GATES 96
#endif
#ifndef WORDS
#define WORDS 2
#endif
#ifndef TARGET_GATES
#define TARGET_GATES 30
#endif
constexpr int N=INPUTS,G=GENOME_GATES,W=WORDS;
struct Gate {int op,a,b;};
using Bits=array<uint64_t,W>;
struct Circuit {array<Gate,G> gates;int r,t;};
array<Bits,N> inputs;Bits rmask{},tmask{},rtarget{},ttarget{};
Circuit initial;
int initial_count;
mt19937_64 rng;
int ri(int n){return rng()%n;}
bitset<G> cone(const Circuit& c){
 array<bool,N+G> used{};used[c.r]=used[c.t]=true;bitset<G> result;
 for(int k=G-1;k>=0;k--)if(used[N+k]){result[k]=true;used[c.gates[k].a]=used[c.gates[k].b]=true;}
 return result;
}
int evaluate(Circuit& c){
 array<Bits,N+G> v;copy(inputs.begin(),inputs.end(),v.begin());
 array<bitset<G>,N+G> uses{};
 vector<int> rs,ts;
 for(int k=0;k<G;k++){
  auto g=c.gates[k];for(int j=0;j<W;j++)v[N+k][j]=g.op?(v[g.a][j]|v[g.b][j]):(v[g.a][j]&v[g.b][j]);
  uses[N+k]=uses[g.a]|uses[g.b];uses[N+k][k]=true;
  bool rok=true,tok=true;
  for(int j=0;j<W;j++){rok &= (v[N+k][j]&rmask[j])==rtarget[j];tok &= (v[N+k][j]&tmask[j])==ttarget[j];}
  if(rok)rs.push_back(N+k);if(tok)ts.push_back(N+k);
 }
 int best=1000000;
 for(int r:rs)for(int t:ts){int count=(uses[r]|uses[t]).count();if(count<best){best=count;c.r=r;c.t=t;}}
 if(best<1000000)return best;
 int wrong=0;
 for(int j=0;j<W;j++){wrong+=popcount((v[c.r][j]^rtarget[j])&rmask[j]);wrong+=popcount((v[c.t][j]^ttarget[j])&tmask[j]);}
 return 10000*wrong+cone(c).count();
}
Circuit seed(){
 Circuit c;array<int,N+G> mapped;for(int i=0;i<N;i++)mapped[i]=i;int original=0;
 for(int slot=0;slot<G;slot++){
  int next_slot=(original+1)*G/(initial_count+1);
  if(original<initial_count&&slot==next_slot){auto g=initial.gates[original];c.gates[slot]={g.op,mapped[g.a],mapped[g.b]};mapped[N+original]=N+slot;original++;}
  else c.gates[slot]={ri(2),ri(N+slot),ri(N+slot)};
 }
 assert(original==initial_count);c.r=mapped[initial.r];c.t=mapped[initial.t];
 return c;
}
void dump(const Circuit& c,const string& path){
 auto used=cone(c);vector<int> selected;
 for(int k=0;k<G;k++)if(used[k])selected.push_back(k);
 array<int,N+G> ren;for(int k=0;k<N;k++)ren[k]=k;
 for(int k=0;k<(int)selected.size();k++)ren[N+selected[k]]=N+k;
 ofstream f(path);f<<"{\"residual_output\":"<<ren[c.r]<<",\"tap_output\":"<<ren[c.t]<<",\"gates\":[\n";
 for(int k=0;k<(int)selected.size();k++){auto g=c.gates[selected[k]];f<<"  ["<<g.op<<","<<ren[g.a]<<","<<ren[g.b]<<"]"<<(k+1<(int)selected.size()?",":"")<<"\n";}f<<"]}\n";
}
int main(int argc,char**argv){
 if(argc!=5){cerr<<"usage: search_two tests-seed.txt seconds seed output-prefix\n";return 2;}
 ifstream f(argv[1]);int m;f>>m;assert(f&&m>0&&m<=64*W);
 for(int j=0;j<m;j++){uint32_t x;int r,t;f>>x>>r>>t;uint64_t b=uint64_t(1)<<(j%64);for(int i=0;i<N;i++)if((x>>i)&1)inputs[i][j/64]|=b;
  assert(f&&x<(uint32_t(1)<<N)&&r>=-1&&r<=1&&t>=-1&&t<=1);
  if(r>=0){rmask[j/64]|=b;if(r)rtarget[j/64]|=b;}if(t>=0){tmask[j/64]|=b;if(t)ttarget[j/64]|=b;}}
 f>>initial_count>>initial.r>>initial.t;assert(f&&initial_count>0&&initial_count<=G&&initial.r>=0&&initial.r<N+initial_count&&initial.t>=0&&initial.t<N+initial_count);
 for(int j=0;j<initial_count;j++){auto&g=initial.gates[j];f>>g.op>>g.a>>g.b;assert(f&&(g.op==0||g.op==1)&&g.a>=0&&g.a<N+j&&g.b>=0&&g.b<N+j);}
 int duration=stoi(argv[2]);rng.seed(stoull(argv[3]));string prefix=argv[4];
 auto begin=chrono::steady_clock::now();long long it=0,restarts=0;int best=100000,lastreport=-1;
 Circuit current=seed();int score=evaluate(current);auto active=cone(current);
 assert(score<10000);cout<<"INITIAL exact active gates "<<score<<endl;dump(current,prefix+"-initial.json");
 while(true){
  double elapsed=chrono::duration<double>(chrono::steady_clock::now()-begin).count();if(elapsed>duration)break;
  if((int)elapsed/10>lastreport){lastreport=(int)elapsed/10;cout<<"seconds "<<elapsed<<" iterations "<<it<<" restarts "<<restarts<<" best "<<best<<" current "<<score<<endl;}
  Circuit next=current;int mutations=1+(ri(5)==0)+(ri(20)==0);
  for(int k=0;k<mutations;k++){
   int j=ri(G);if(ri(2)){while(!active[j])j=ri(G);}int mode=ri(12);
   if(mode<5)next.gates[j].a=ri(N+j);else if(mode<10)next.gates[j].b=ri(N+j);else next.gates[j].op^=1;
  }
  int ns=evaluate(next);
  if(ns<best){best=ns;dump(next,prefix+"-best.json");cout<<"BEST "<<best<<" at "<<elapsed<<endl;}
  if(ns<=TARGET_GATES){dump(next,prefix+"-solution.json");cout<<"SOLUTION "<<prefix<<"-solution.json"<<endl;return 0;}
  double temp=((it/1000000)%3==0)?0.1:(((it/1000000)%3==1)?0.7:2.0);
  if(ns<=score || uniform_real_distribution<double>(0,1)(rng)<exp((score-ns)/temp)){current=next;score=ns;active=cone(current);}
  ++it;
  if(it%10000000==0){current=seed();score=evaluate(current);active=cone(current);restarts++;}
 }
 cout<<"DONE iterations "<<it<<" best "<<best<<endl;
}
