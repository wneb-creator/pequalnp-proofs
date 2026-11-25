#include <array>
#include <vector>
#include <random>
#include <chrono>
#include <cmath>
#include <iostream>
#include <algorithm>
using namespace std;
using Word=unsigned long long;
using Bits=array<Word,16>;
struct Gate {int op,a,b;};
using Circuit=array<Gate,19>;
mt19937 rng(1042592);
array<Bits,11> inputs;
Bits target;
vector<pair<int,int>> edges={{0,1},{1,2},{2,3},{3,4},{4,0},{0,5},{1,6},{2,7},{3,8},{4,9},{5,7},{7,9},{9,6},{6,8},{8,5}};
vector<int> covers;
int score(const Circuit& c){
 array<Bits,30> w;
 for(int j=0;j<11;j++) w[j]=inputs[j];
 bool hasnot=false;
 for(int i=0;i<19;i++){
  auto g=c[i];hasnot|=g.op==2;
  for(int k=0;k<16;k++) w[11+i][k]=g.op==0?(w[g.a][k]&w[g.b][k]):g.op==1?(w[g.a][k]|w[g.b][k]):~w[g.a][k];
 }
 int s=0;
 for(int k=0;k<16;k++)s+=__builtin_popcountll(w[29][k]&~target[k])*8+__builtin_popcountll(~w[29][k]&target[k]);
 return s+(hasnot?0:10);
}
void show(const Circuit& c,int s,long long trial){
 cout<<"best "<<s<<" trial "<<trial<<" gates [";
 for(auto g:c)cout<<"("<<g.op<<","<<g.a<<","<<g.b<<"),";
 cout<<"]"<<endl;
}
Circuit seed(){
 int cover=covers[rng()%covers.size()];
 array<vector<int>,10> star;
 for(auto [a,b]:edges){if((cover>>a&1)&&(cover>>b&1)){if(rng()%2)swap(a,b);}else if(!(cover>>a&1))swap(a,b);star[a].push_back(b);}
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
 // Gate indexing is 11+i, accounting for free false source10.
 while(g.size()>19){
  int d=rng()%(g.size()-1);int replacement=(rng()%2)?g[d].a:g[d].b;
  int wire=11+d;
  for(size_t i=d+1;i<g.size();i++)for(int *p:{&g[i].a,&g[i].b}){
   if(*p==wire)*p=replacement;else if(*p>wire)--*p;
  }
  g.erase(g.begin()+d);
 }
 while(g.size()<19)g.push_back({1,int(10+g.size()),10});
 Circuit c;copy(g.begin(),g.end(),c.begin());
 c[rng()%19].op=2;
 return c;
}
int main(){
 for(int x=0;x<1024;x++){
  for(int j=0;j<10;j++)if(x>>j&1)inputs[j][x/64]|=1ULL<<(x%64);
  for(auto [a,b]:edges)if((x>>a&1)&&(x>>b&1)){target[x/64]|=1ULL<<(x%64);break;}
 }
 for(int c=0;c<1024;c++)if(__builtin_popcount((unsigned)c)==6){bool yes=true;for(auto[a,b]:edges)if(!(c>>a&1)&&!(c>>b&1))yes=false;if(yes)covers.push_back(c);}
 auto start=chrono::steady_clock::now();
 int global=10000;Circuit best;long long trial=0;
 for(int run=0;run<100000;run++){
  Circuit c=seed(),local=c;int s=score(c),loc=s;
  for(int iter=0;iter<200000;iter++,trial++){
   if(trial%100000==0 && chrono::duration<double>(chrono::steady_clock::now()-start).count()>300){cout<<"done "<<trial<<" best "<<global<<endl;return 0;}
   Circuit d=c;
   int mutations=(rng()%32==0)?2:1;
   while(mutations--){int i=rng()%19,t=rng()%5;if(t==0)d[i].op=rng()%3;else if(t<3)d[i].a=rng()%(11+i);else d[i].b=rng()%(11+i);}
   int ds=score(d);
   double temp=1.0+5.0*(1.0-double(iter%20000)/20000.0);
   bool accept=ds<=s || (double(rng())/rng.max()<exp(double(s-ds)/temp));
   if(accept){c=d;s=ds;}
   if(s<loc){local=c;loc=s;}
   if(s<global){best=c;global=s;show(best,global,trial);if(global==0)return 0;}
   if(iter%20000==19999){c=local;s=loc;}
  }
 }
}
