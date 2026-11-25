#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <map>
#include <unordered_map>
#include <vector>
using namespace std;
struct Info {int edgeMask; int count; int minsize=999; bool star=false; vector<array<int,3>> circuit;};
int n, limit; uint64_t allmask, nodes=0; vector<pair<int,int>> pairs; unordered_map<uint64_t,Info> targets;
vector<uint64_t> wire; vector<uint32_t> cone; vector<array<int,3>> gates;
bool star(const Info &info) {
 for(int k=0;k<(int)gates.size();k++) if(gates[k][0]==0) {
  int center=(1<<n)-1; bool any=false;
  for(int e=0;e<(int)pairs.size();e++) if(info.edgeMask>>e&1) {
   auto [u,v]=pairs[e]; int input=(1<<u)|(1<<v);
   if(!(wire[n+k]>>input&1)) continue;
   bool owned=true;
   for(int j=0;j<k;j++) if((cone[n+k]>>j&1) && gates[j][0]==0 && (wire[n+j]>>input&1)) { owned=false;break; }
   if(owned) {any=true;center&=input;}
  }
  if(!any || !center) return false;
 }
 return true;
}
void dfs(int depth) {
 nodes++;
 if(depth) {
  auto it=targets.find(wire.back());
  if(it!=targets.end()) {auto &a=it->second;
   if(depth<a.minsize) {a.minsize=depth;a.star=false;a.circuit=gates;}
   if(depth==a.minsize && !a.star && star(a)) {a.star=true;a.circuit=gates;}
  }
 }
 if(depth==limit) return;
 int w=wire.size();
 for(int a=0;a<w;a++) for(int b=a+1;b<w;b++) for(int op=0;op<2;op++) {
  uint64_t f=op?(wire[a]|wire[b]):(wire[a]&wire[b]);
  if(f==0||f==allmask||find(wire.begin(),wire.end(),f)!=wire.end()) continue;
  uint32_t c=cone[a]|cone[b];
  if(a>=n)c|=1u<<(a-n); if(b>=n)c|=1u<<(b-n);
  wire.push_back(f);cone.push_back(c);gates.push_back({op,a,b});
  dfs(depth+1);
  gates.pop_back();cone.pop_back();wire.pop_back();
 }
}
int main(int argc,char**argv) {
 n=argc>1?atoi(argv[1]):4;limit=argc>2?atoi(argv[2]):4;
 if(n>6) return 2;
 for(int i=0;i<n;i++)for(int j=i+1;j<n;j++) pairs.push_back({i,j});
 for(int em=1;em<(1<<(int)pairs.size());em++) {
  bool adj[6][6]={};int ec=0;
  for(int e=0;e<(int)pairs.size();e++)if(em>>e&1){auto[u,v]=pairs[e];adj[u][v]=adj[v][u]=true;ec++;}
  bool okay=true;
  for(int a=0;a<n;a++)for(int b=0;b<n;b++)for(int c=0;c<n;c++) {
   if(adj[a][b]&&adj[b][c]&&adj[c][a])okay=false;
   if(a==c)continue;
   int common=0;for(int d=0;d<n;d++)common+=adj[a][d]&&adj[c][d];
   if(common>=2)okay=false;
  }
  if(!okay)continue;
  uint64_t tt=0;
  for(int x=0;x<(1<<n);x++)for(int e=0;e<(int)pairs.size();e++)if(em>>e&1){auto[u,v]=pairs[e];if((x>>u&1)&&(x>>v&1)){tt|=1ull<<x;break;}}
  targets.emplace(tt,Info{em,ec});
 }
 allmask=n==6?~0ull:((1ull<<(1<<n))-1);
 for(int i=0;i<n;i++){uint64_t tt=0;for(int x=0;x<(1<<n);x++)if(x>>i&1)tt|=1ull<<x;wire.push_back(tt);cone.push_back(0);}
 dfs(0);
 map<pair<int,bool>,int> summary;int seen=0;
 for(auto &[tt,a]:targets){summary[{a.minsize,a.star}]++;if(a.minsize<999)seen++;}
 cout<<"n="<<n<<" limit="<<limit<<" nodes="<<nodes<<" graphs="<<targets.size()<<" found="<<seen<<"\n";
 for(auto [k,c]:summary)cout<<"minimum="<<k.first<<" star="<<k.second<<" graphs="<<c<<"\n";
 for(auto &[tt,a]:targets)if(a.minsize<999&&!a.star)cout<<"WARNING nonstar-only minimum graph="<<a.edgeMask<<" minimum="<<a.minsize<<"\n";
}
