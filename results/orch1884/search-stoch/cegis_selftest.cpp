#include <array>
#include <vector>
#include <random>
#include <chrono>
#include <cmath>
#include <iostream>
#include <algorithm>
#include <csignal>
using namespace std;
using Word=unsigned long long;
using Bits=array<Word,16>;
struct Gate {int op,a,b;};
using Circuit=array<Gate,32>;
mt19937 rng(188401);
volatile sig_atomic_t stopFlag=0;
void stopped(int){stopFlag=1;}
array<Bits,11> inputs;
Bits target;
vector<pair<int,int>> edges={{0,1},{1,2},{2,3},{3,4},{4,0},{0,5},{1,6},{2,7},{3,8},{4,9},{5,7},{7,9},{9,6},{6,8},{8,5}};
vector<int> covers;
vector<int> samples={3,6,12,13,17,24,33,50,66,69,104,116,132,133,138,160,200,201,208,264,265,276,288,320,321,385,402,521,528,548,554,576,577,640,641,770,772,773};
int blocks=1;
Bits rowMasks{};
void rebuild(){
 for(auto& b:inputs)b.fill(0);target.fill(0);rowMasks.fill(0);blocks=(samples.size()+63)/64;
 for(size_t r=0;r<samples.size();r++){int x=samples[r];rowMasks[r/64]|=1ULL<<(r%64);for(int j=0;j<10;j++)if(x>>j&1)inputs[j][r/64]|=1ULL<<(r%64);for(auto[a,b]:edges)if((x>>a&1)&&(x>>b&1)){target[r/64]|=1ULL<<(r%64);break;}}
 for(int k=0;k<blocks;k++)inputs[10][k]=~inputs[0][k]&rowMasks[k];
 cout<<"SAMPLES [";for(size_t r=0;r<samples.size();r++){if(r)cout<<",";cout<<samples[r];}cout<<"]"<<endl;
}
bool refine(const Circuit&c){
 vector<int>errors;
 for(int x=0;x<1024;x++){
  array<bool,43>w{};for(int j=0;j<10;j++)w[j]=(x>>j)&1;w[10]=!w[0];
  for(int i=0;i<32;i++){auto g=c[i];w[11+i]=g.op==0?(w[g.a]&&w[g.b]):g.op==1?(w[g.a]||w[g.b]):!w[g.a];}
  bool want=false;for(auto[a,b]:edges)want|=(x>>a&1)&&(x>>b&1);if(w[42]!=want)errors.push_back(x);
 }
 if(errors.empty()){
  cout<<"SELFTEST_BASELINE {\"inputs\":11,\"output\":42,\"gates\":[";for(int i=0;i<32;i++){if(i)cout<<",";auto g=c[i];cout<<"["<<g.op<<","<<g.a<<","<<g.b<<"]";}cout<<"]}"<<endl;return true;
 }
 shuffle(errors.begin(),errors.end(),rng);int added=0;
 for(int x:errors)if(find(samples.begin(),samples.end(),x)==samples.end()){samples.push_back(x);if(++added==16)break;}
 if(!added){cerr<<"FAULT zero sampled error disagrees with full validation"<<endl;exit(2);}
 cout<<"REFINE full_errors "<<errors.size()<<" added "<<added<<" rows "<<samples.size()<<endl;rebuild();return false;
}

int score(const Circuit& c){
 array<Bits,43> w;
 for(int j=0;j<11;j++) w[j]=inputs[j];
 bool hasnot=false;
 for(int i=0;i<32;i++){
  auto g=c[i];hasnot|=g.op==2;
  for(int k=0;k<blocks;k++) w[11+i][k]=g.op==0?(w[g.a][k]&w[g.b][k]):g.op==1?(w[g.a][k]|w[g.b][k]):~w[g.a][k];
 }
 int s=0;
 for(int k=0;k<blocks;k++)s+=__builtin_popcountll(w[42][k]&~target[k]&rowMasks[k])*4+__builtin_popcountll(~w[42][k]&target[k]&rowMasks[k]);
 return s;
}
void show(const Circuit& c,int s,long long trial){
 cout<<"best "<<s<<" trial "<<trial<<" gates [";
 for(auto g:c)cout<<"("<<g.op<<","<<g.a<<","<<g.b<<"),";
 cout<<"]"<<endl;
}
Circuit seed(){
 int cover=covers[rng()%covers.size()];int dropA=15,dropB=16;int ei=0;
 array<vector<int>,10> star;
 for(auto [a,b]:edges){int edgei=ei++;if(edgei==dropA||edgei==dropB)continue;if((cover>>a&1)&&(cover>>b&1)){if(rng()%2)swap(a,b);}else if(!(cover>>a&1))swap(a,b);star[a].push_back(b);}
 vector<int> centers;for(int v=0;v<10;v++)if(!star[v].empty())centers.push_back(v);
 shuffle(centers.begin(),centers.end(),rng);
 vector<Gate> g;vector<int> roots;
 for(int v:centers){
  shuffle(star[v].begin(),star[v].end(),rng);int cur=star[v][0];
  for(size_t j=1;j<star[v].size();j++){g.push_back({1,cur,star[v][j]});cur=10+g.size();}
  g.push_back({0,v,cur});roots.push_back(10+g.size());
 }
 shuffle(roots.begin(),roots.end(),rng);
 int cur=roots[0];
 for(size_t j=1;j<roots.size();j++){g.push_back({1,cur,roots[j]});cur=10+g.size();}
 // Gate indexing is 11+i, accounting for free NOT(input0) source10.
 while(g.size()>32){
  int d=rng()%(g.size()-1);int replacement=(rng()%2)?g[d].a:g[d].b;
  int wire=11+d;
  for(size_t i=d+1;i<g.size();i++)for(int *p:{&g[i].a,&g[i].b}){
   if(*p==wire)*p=replacement;else if(*p>wire)--*p;
  }
  g.erase(g.begin()+d);
 }
 while(g.size()<32)g.push_back({0,int(10+g.size()),int(10+g.size())});
 Circuit c;copy(g.begin(),g.end(),c.begin());
 
 return c;
}

array<Bits,43> values(const Circuit& c){
 array<Bits,43> w;
 for(int j=0;j<11;j++) w[j]=inputs[j];
 for(int i=0;i<32;i++){
  auto g=c[i];
  for(int k=0;k<blocks;k++) w[11+i][k]=g.op==0?(w[g.a][k]&w[g.b][k]):g.op==1?(w[g.a][k]|w[g.b][k]):~w[g.a][k];
 }
 return w;
}
Bits forceOutput(const Circuit& c,array<Bits,43> w,int i,Word val){
 w[11+i].fill(val);
 for(int j=i+1;j<32;j++){
  auto g=c[j];
  for(int k=0;k<blocks;k++) w[11+j][k]=g.op==0?(w[g.a][k]&w[g.b][k]):g.op==1?(w[g.a][k]|w[g.b][k]):~w[g.a][k];
 }
 return w[42];
}
int coordinate(Circuit& c,int i,int temperature){
 auto w=values(c);Bits f0=forceOutput(c,w,i,0),f1=forceOutput(c,w,i,~0ULL);
 Bits care,want,negative;
 for(int k=0;k<blocks;k++){care[k]=(f0[k]^f1[k])&rowMasks[k];want[k]=target[k]^f0[k];negative[k]=~target[k];}
 int nn=0;for(int j=0;j<32;j++)if(j!=i&&c[j].op==2)nn++;
 int best=1000000,count=0;Gate selected=c[i];
 for(int op=0;op<3;op++)for(int a=0;a<11+i;a++)for(int b=(op==2?a:0);b<=(op==2?a:a);b++){
  if(op==2&&nn>0)continue;int sc=0;
  for(int k=0;k<blocks;k++){
   Word v=op==0?(w[a][k]&w[b][k]):op==1?(w[a][k]|w[b][k]):~w[a][k];
   Word err=(v^want[k])&care[k];
   sc+=__builtin_popcountll(err)+3*__builtin_popcountll(err&negative[k]);
  }
  if(temperature>0)sc+=rng()%(temperature+1);
  if(sc<best){best=sc;count=1;selected={op,a,b};}
  else if(sc==best&&rng()%++count==0)selected={op,a,b};
 }
 c[i]=selected;return score(c);
}

int main(){
 rng.seed(188444);rebuild();
 for(int c=0;c<1024;c++)if(__builtin_popcount((unsigned)c)==6){bool yes=true;for(auto[a,b]:edges)if(!(c>>a&1)&&!(c>>b&1))yes=false;if(yes)covers.push_back(c);}
 Circuit c=seed();if(score(c)!=0||!refine(c))return 2;
 c[20]={1,1,2};for(int i=21;i<=27;i++)c[i]={1,10+i,i-18};
 c[28]={2,38,38};c[29]={0,0,39};c[30]={1,30,40};c[31]={0,41,41};
 if(score(c)!=0)return 3;
 if(refine(c))return 4;
 if(samples.back()!=1||score(c)!=4)return 5;
 cout<<"SELFTEST_PASS fullcube correct baseline; isolated hidden false positive caught and added"<<endl;return 0;
}
