#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <random>
#include <vector>
using namespace std;
constexpr int N=19,W=16;
struct Gate {int op,a,b;};
using Circuit=array<Gate,N>;
using Truth=array<uint64_t,W>;
array<Truth,10+N> table;
Truth target,weights[4];
pair<int,int> edges[15]={{0,1},{1,2},{2,3},{3,4},{4,0},{0,5},{1,6},{2,7},{3,8},{4,9},{5,7},{7,9},{9,6},{6,8},{8,5}};
mt19937_64 rng;
bool requireActive=false;
int randn(int n){return rng()%n;}
int evaluate(const Circuit&c){
 int negs=0;
 for(int i=0;i<N;i++){
  auto g=c[i];negs+=g.op==2;
  for(int j=0;j<W;j++)table[i+10][j]=g.op==0?(table[g.a][j]&table[g.b][j]):g.op==1?(table[g.a][j]|table[g.b][j]):~table[g.a][j];
 }
 if(requireActive){
  array<bool,N+10> active={};active[N+9]=true;negs=0;
  for(int i=N-1;i>=0;i--)if(active[i+10]){auto g=c[i];active[g.a]=true;if(g.op!=2)active[g.b]=true;else negs++;}
 }
 int score=negs?0:10000;
 for(int j=0;j<W;j++){
  auto diff=table[10+N-1][j]^target[j];
  score+=__builtin_popcountll(diff);
  score+=12*__builtin_popcountll(diff&weights[0][j]);
  score+=6*__builtin_popcountll(diff&weights[1][j]);
 }
 return score;
}
Circuit randomC(){Circuit c; for(int i=0;i<N;i++)c[i]={randn(20)==0?2:randn(2),randn(i+10),randn(i+10)};c[randn(N)].op=2;return c;}
Circuit seed(){
 int indep[5][4]={{0,2,8,9},{0,3,6,7},{1,3,5,9},{1,4,7,8},{2,4,5,6}};
 bool inside[10]={};for(int x:indep[randn(5)])inside[x]=true;
 vector<int> allocated[10];
 for(auto [a,b]:edges){int v=inside[a]?b:inside[b]?a:(randn(2)?a:b);allocated[v].push_back(a^b^v);}
 vector<int> order;for(int v=0;v<10;v++)if(!allocated[v].empty())order.push_back(v);
 shuffle(order.begin(),order.end(),rng);
 vector<Gate> gs;vector<int> outputs;
 for(int v:order){shuffle(allocated[v].begin(),allocated[v].end(),rng);int acc=allocated[v][0];for(int k=1;k<(int)allocated[v].size();k++){gs.push_back({1,acc,allocated[v][k]});acc=9+gs.size();}gs.push_back({0,acc,v});outputs.push_back(9+gs.size());}
 while(outputs.size()>1){int a=outputs.back();outputs.pop_back();int k=randn(outputs.size());int b=outputs[k];gs.push_back({1,a,b});outputs[k]=9+gs.size();}
 while(gs.size()>N){int del=randn(gs.size()-1);auto old=gs[del];int repl=randn(2)?old.a:old.b;gs.erase(gs.begin()+del);for(int i=del;i<(int)gs.size();i++){for(int* x:{&gs[i].a,&gs[i].b}){if(*x==10+del)*x=repl;else if(*x>10+del)(*x)--;}}}
 while(gs.size()<N){for(auto &g:gs){g.a++;g.b++;}gs.insert(gs.begin(),{2,0,0});}
 Circuit c;copy(gs.begin(),gs.end(),c.begin());c[randn(N)].op=2;return c;
}
void show(Circuit c,int score,uint64_t evaluations){cout<<"score "<<score<<" evaluations "<<evaluations<<"\n";for(int i=0;i<N;i++)cout<<10+i<<" "<<c[i].op<<" "<<c[i].a<<" "<<c[i].b<<"\n";cout<<flush;}
int main(int argc,char**argv){
 int seconds=argc>1?atoi(argv[1]):600;uint64_t seedValue=argc>2?strtoull(argv[2],nullptr,10):1;rng.seed(seedValue);requireActive=argc>3;
 for(int x=0;x<1024;x++){
  for(int i=0;i<10;i++)if(x>>i&1)table[i][x/64]|=1ULL<<(x%64);
  bool val=false;for(auto[a,b]:edges)val|=(x>>a&1)&&(x>>b&1);if(val)target[x/64]|=1ULL<<(x%64);
  if(!val)weights[0][x/64]|=1ULL<<(x%64);
  if(val&&__builtin_popcount((unsigned)x)==2)weights[1][x/64]|=1ULL<<(x%64);
 }
 auto start=chrono::steady_clock::now();uint64_t count=0;int best=100000;Circuit bestC;
 while(chrono::duration<double>(chrono::steady_clock::now()-start).count()<seconds){
  Circuit c=randn(2)?seed():randomC();int score=evaluate(c);count++;
  for(int t=0;t<50000;t++){
   Circuit d=c;int nmut=1+(randn(10)==0?randn(5):0);
   for(int m=0;m<nmut;m++){int k=randn(N),what=randn(3);auto &g=d[k];if(what==0)g.op=randn(12)==0?2:randn(2);else if(what==1)g.a=randn(10+k);else g.b=randn(10+k);}
   int ds=evaluate(d);count++;
   if(ds<best){best=ds;bestC=d;show(d,ds,count);if(ds==0)return 0;}
   if(ds<=score){c=d;score=ds;}
   if((count&0xFFFFF)==0&&chrono::duration<double>(chrono::steady_clock::now()-start).count()>=seconds)break;
  }
 }
 cout<<"completed seconds "<<seconds<<" seed "<<seedValue<<" evaluations "<<count<<" best "<<best<<"\n";
}
