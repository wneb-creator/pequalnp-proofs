#include <array>
#include <vector>
#include <random>
#include <iostream>
#include <chrono>
#include <algorithm>
#include <cstdlib>
using namespace std;
using U=unsigned long long;
using TT=array<U,16>;
struct Gate { int op,a,b; };
struct Circ { array<Gate,20> g; int n; };
const vector<pair<int,int>> edges={{0,1},{1,2},{2,3},{3,4},{4,0},{0,5},{1,6},{2,7},{3,8},{4,9},{5,7},{7,9},{9,6},{6,8},{8,5}};
array<TT,12> inputs; TT target,edgeMask,negMask;
mt19937 rng(134);
bool requireFirst=false;
int ri(int n){return rng()%n;}
int score(const Circ& c, int *raw=nullptr) {
 array<TT,32> w;
 for(int i=0;i<12;i++)w[i]=inputs[i];
 for(int i=0;i<c.n;i++) {
  auto g=c.g[i];
  for(int k=0;k<16;k++)w[12+i][k]=g.op==0?(w[g.a][k]&w[g.b][k]):g.op==1?(w[g.a][k]|w[g.b][k]):~w[g.a][k];
 }
 int result=0,r=0;
 for(int k=0;k<16;k++) {U d=w[11+c.n][k]^target[k]; r+=__builtin_popcountll(d);result+=__builtin_popcountll(d)+16*__builtin_popcountll(d&edgeMask[k])+4*__builtin_popcountll(d&negMask[k]);}
 if(requireFirst){array<bool,32> active{};active[11+c.n]=true;for(int i=c.n-1;i>=0;i--)if(active[12+i]){active[c.g[i].a]=true;if(c.g[i].op!=2)active[c.g[i].b]=true;}if(!active[12])result+=1000;}
 if(raw)*raw=r;
 return result;
}
vector<Circ> seeds;
void setup() {
 for(int x=0;x<1024;x++) {
  for(int i=0;i<10;i++) if(x>>i&1) inputs[i][x/64]|=1ull<<(x%64);
  if((x&5)==5)inputs[10][x/64]|=1ull<<(x%64);
  bool t=false; for(auto [a,b]:edges)t|=((x>>a&1)&&(x>>b&1));
  if(t)target[x/64]|=1ull<<(x%64); else negMask[x/64]|=1ull<<(x%64);
  if(t&&__builtin_popcount((unsigned)x)==2)edgeMask[x/64]|=1ull<<(x%64);
 }
 for(int cover=0;cover<1024;cover++)if(__builtin_popcount((unsigned)cover)==6) {
  bool ok=true;for(auto[a,b]:edges)if(!(cover>>a&1)&&!(cover>>b&1))ok=false;if(!ok)continue;
  for(int rep=0;rep<20;rep++) {
   array<vector<int>,10> adj;
   for(auto[a,b]:edges){if(!(cover>>a&1))swap(a,b);else if((cover>>b&1)&&ri(2))swap(a,b);adj[a].push_back(b);}
   Circ c{};vector<int> stars;
   for(int a=0;a<10;a++)if(!adj[a].empty()) {
    shuffle(adj[a].begin(),adj[a].end(),rng);int y=adj[a][0];
    for(int j=1;j<(int)adj[a].size();j++){c.g[c.n]={1,y,adj[a][j]};y=12+c.n++;}
    c.g[c.n]={0,a,y};stars.push_back(12+c.n++);
   }
   shuffle(stars.begin(),stars.end(),rng);int y=stars[0];
   for(int j=1;j<(int)stars.size();j++){c.g[c.n]={1,y,stars[j]};y=12+c.n++;}
   if(score(c)==0)seeds.push_back(c);
  }
 }
}
Circ shrink(Circ c,int n){while(c.n>n){int k=ri(c.n-1);int repl=ri(3)==0?10:(ri(2)?c.g[k].a:c.g[k].b);for(int j=k+1;j<c.n;j++){auto &g=c.g[j];for(int *p:{&g.a,&g.b}){if(*p==12+k)*p=repl;if(*p>12+k)--*p;}}for(int j=k;j+1<c.n;j++)c.g[j]=c.g[j+1];--c.n;}return c;}
void print(const Circ& c){for(int i=0;i<c.n;i++)cout<<12+i<<":"<<c.g[i].op<<","<<c.g[i].a<<","<<c.g[i].b<<" ";cout<<endl;}
int main(int argc,char**argv){int sec=argc>1?atoi(argv[1]):600;int n=argc>2?atoi(argv[2]):18;bool forceNot=argc>3;requireFirst=argc>4;setup();cout<<"seeds "<<seeds.size()<<" force-not-seed "<<forceNot<<" require-first "<<requireFirst<<endl;int best=100000;auto start=chrono::steady_clock::now();long long iters=0;for(int run=0;;run++){
 Circ c=shrink(seeds[ri(seeds.size())],n-(forceNot?1:0));
 if(forceNot){for(int i=c.n;i>0;i--){c.g[i]=c.g[i-1];if(c.g[i].a>=12)c.g[i].a++;if(c.g[i].b>=12)c.g[i].b++;}c.g[0]={2,10,0};c.n++;}
 int sc=score(c),last=0;
 for(int j=0;j<100000;j++,iters++){
  if((iters&65535)==0&&chrono::duration_cast<chrono::seconds>(chrono::steady_clock::now()-start).count()>=sec){cout<<"DONE best "<<best<<" iterations "<<iters<<endl;return 0;}
  Circ d=c;int muts=ri(12)==0?2+ri(3):1;
  for(int z=0;z<muts;z++){int k=forceNot?1+ri(n-1):ri(n),v=ri(3);if(v==0)d.g[k].op=forceNot?ri(2):(ri(20)<2?2:ri(2));else if(v==1)d.g[k].a=ri(12+k);else d.g[k].b=ri(12+k);}
  int ds=score(d);
  if(ds<=sc){if(ds<sc)last=j;c=d;sc=ds;}
  if(sc<best){best=sc;int raw;score(c,&raw);cout<<"BEST "<<best<<" raw "<<raw<<" iter "<<iters<<" run "<<run<<endl;print(c);if(sc==0)return 0;}
  if(j-last>10000)break;
 }
}}
