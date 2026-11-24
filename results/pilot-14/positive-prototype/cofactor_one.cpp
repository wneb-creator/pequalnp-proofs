#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <map>
#include <set>
#include <unordered_map>
#include <unordered_set>
#include <vector>
using namespace std;
using U=uint64_t;
static constexpr int W=7;
struct Bits {array<U,W> a{}; bool operator==(const Bits& b) const {return a==b.a;} bool operator<(const Bits& b) const {return a<b.a;}};
Bits operator|(Bits a,const Bits& b){for(int i=0;i<W;i++)a.a[i]|=b.a[i];return a;}
Bits operator&(Bits a,const Bits& b){for(int i=0;i<W;i++)a.a[i]&=b.a[i];return a;}
Bits operator^(Bits a,const Bits& b){for(int i=0;i<W;i++)a.a[i]^=b.a[i];return a;}
Bits operator~(Bits a){for(auto&v:a.a)v=~v;return a;}
struct Sig{Bits p,n;bool operator==(const Sig& b)const{return p==b.p&&n==b.n;}};
size_t mix(size_t h,U x){return h^(x+0x9e3779b97f4a7c15ULL+(h<<6)+(h>>2));}
struct SH{size_t operator()(const Sig&s)const{size_t h=1;for(U x:s.p.a)h=mix(h,x);for(U x:s.n.a)h=mix(h,x);return h;}};
struct State{vector<int> v;int k,t;bool operator==(const State&b)const{return k==b.k&&t==b.t&&v==b.v;}};
struct StH{size_t operator()(const State&s)const{size_t h=s.k*8+s.t;for(int x:s.v)h=mix(h,x);return h;}};
struct Signal{Sig s;Bits sep[2];int ng=-1;int op=-1,pa=-1,pb=-1;array<int,12> acts;};
vector<array<int,9>> autos;vector<int> raw;
vector<Signal> signals;unordered_map<Sig,int,SH> ids;unordered_map<U,int> bins;unordered_set<State,StH> failed;
Bits top;int goal;uint64_t nodes=0,hits=0,branches=0;array<uint64_t,32> depths{};chrono::steady_clock::time_point started;double seconds;bool stopped=false;uint64_t maxnodes;
int intern(Sig s){auto it=ids.find(s);if(it!=ids.end())return it->second;int id=signals.size();Signal z;z.s=s;z.sep[0]=s.p&~s.n;z.sep[1]=s.p^s.n;z.acts.fill(-1);signals.push_back(z);ids.emplace(s,id);return id;}
int neg(int a){if(signals[a].ng>=0)return signals[a].ng;Sig s=signals[a].s;int b=intern({s.p^top,s.n^top});if(signals[b].op<0){signals[b].op=2;signals[b].pa=a;}signals[a].ng=b;signals[b].ng=a;return b;}
int binary(int a,int b,int op){if(a>b)swap(a,b);U key=((U)a<<33)|((U)b<<1)|op;auto it=bins.find(key);if(it!=bins.end())return it->second;Sig x=signals[a].s,y=signals[b].s;int r=intern(op?Sig{x.p|y.p,x.n|y.n}:Sig{x.p&y.p,x.n&y.n});if(signals[r].op<0){signals[r].op=op;signals[r].pa=a;signals[r].pb=b;}bins.emplace(key,r);return r;}
int action(int a,int g){if(signals[a].acts[g]>=0)return signals[a].acts[g];int op=signals[a].op,pa=signals[a].pa,pb=signals[a].pb;int b;if(op==2)b=neg(action(pa,g));else if(op<2&&op>=0)b=binary(action(pa,g),action(pb,g),op);else {cerr<<"bad recipe "<<a<<" op="<<op<<"\n";abort();}signals[a].acts[g]=b;return b;}
vector<int> canonical(const vector<int>&v){vector<int> best=v;for(int g=1;g<(int)autos.size();g++){vector<int>w;for(int a:v)w.push_back(action(a,g));sort(w.begin(),w.end());if(w<best)best=move(w);}return best;}
bool search(vector<int>v,int k,int t);
bool attempt(const vector<int>&v,const vector<int>&rest,int a,int b,int g,int k,int t,int kind){
 if(g==0||g==1||binary_search(v.begin(),v.end(),g))return false;
 for(int keep=0;keep<(b<0?2:4);keep++){
  int n=rest.size()+1+__builtin_popcount((unsigned)keep);if(n>k-t+1)continue;
  Bits cover=signals[g].sep[t>0];for(int q:rest)cover=cover|signals[q].sep[t>0];
  if(keep&1)cover=cover|signals[a].sep[t>0];if(keep&2)cover=cover|signals[b].sep[t>0];
  if(!(cover==top))continue;
  vector<int>w=rest;w.push_back(g);if(keep&1)w.push_back(a);if(keep&2)w.push_back(b);sort(w.begin(),w.end());branches++;
  if(search(w,k,t)){cerr<<"move k="<<k+1<<" t="<<t+(kind==2)<<" op="<<kind<<" a="<<a<<" b="<<b<<" g="<<g<<" keep="<<keep<<"\n";return true;}
  if(stopped)return false;
 }
 return false;
}
bool search(vector<int>v,int k,int t){
 nodes++;depths[k]++;
 if((nodes&65535)==0){double elapsed=chrono::duration<double>(chrono::steady_clock::now()-started).count();if(elapsed>seconds||nodes>maxnodes){stopped=true;return false;}if((nodes&1048575)==0)cerr<<"progress nodes="<<nodes<<" sec="<<elapsed<<" failed="<<failed.size()<<" signals="<<signals.size()<<" bins="<<bins.size()<<"\n";}
 if(v.size()==1&&v[0]==goal)return true;
 if(k==0||t>k||v.size()>(unsigned)(k-t+1))return false;
 v=canonical(v);State key{v,k,t};if(failed.count(key)){hits++;return false;}
 int n=v.size();
 // Binary steps first consume both operands, then retain where budget permits.
 for(int a=0;a<n;a++)for(int b=a+1;b<n;b++){
  vector<int>rest;for(int i=0;i<n;i++)if(i!=a&&i!=b)rest.push_back(v[i]);
  for(int op=0;op<2;op++){int g=binary(v[a],v[b],op);if(attempt(v,rest,v[a],v[b],g,k-1,t,op))return true;if(stopped)return false;}
 }
 if(t>0)for(int a=0;a<n;a++){
  vector<int>rest=v;rest.erase(rest.begin()+a);int g=neg(v[a]);if(attempt(v,rest,v[a],-1,g,k-1,t-1,2))return true;if(stopped)return false;
 }
 failed.insert(move(key));return false;
}
int main(int argc,char**argv){
 seconds=argc>1?atof(argv[1]):30;maxnodes=argc>2?strtoull(argv[2],0,10):10000000;int maxk=argc>3?atoi(argv[3]):15;int initialt=argc>4?atoi(argv[4]):0;
 vector<pair<int,int>> E={{0,1},{1,2},{2,3},{3,4},{4,0},{0,5},{1,6},{2,7},{3,8},{5,7},{6,8},{8,5}};
 auto f=[&](int x){for(auto [a,b]:E)if((x>>a&1)&&(x>>b&1))return true;return false;};
 vector<int>ind,mis;for(int x=0;x<512;x++)if(!f(x))ind.push_back(x);for(int x:ind){bool maximal=true;for(int i=0;i<9;i++)if(!(x>>i&1)&&!f(x|(1<<i)))maximal=false;if(maximal)mis.push_back(x);}
 set<pair<int,int>> pairset;for(int y:ind)for(int i=0;i<9;i++)if(f(y^(1<<i)))pairset.emplace(y^(1<<i),y);for(auto [a,b]:E)for(int y:mis)pairset.emplace((1<<a)|(1<<b),y);
 vector<pair<int,int>>pairs(pairset.begin(),pairset.end());pairs.erase(remove_if(pairs.begin(),pairs.end(),[](auto xy){return !(xy.first>>4&1)||!(xy.second>>4&1);}),pairs.end());cerr<<"pairs="<<pairs.size()<<" independent="<<ind.size()<<" maximal="<<mis.size()<<"\n";if(pairs.size()>W*64)return 3;
 for(int j=0;j<(int)pairs.size();j++)top.a[j/64]|=1ULL<<(j%64);
 intern({{}, {}});intern({top,top});goal=intern({top,{}});vector<int>root;
 for(int i=0;i<9;i++){Sig s;for(int j=0;j<(int)pairs.size();j++){if(pairs[j].first>>i&1)s.p.a[j/64]|=1ULL<<(j%64);if(pairs[j].second>>i&1)s.n.a[j/64]|=1ULL<<(j%64);}root.push_back(intern(s));}
 raw=root;root.erase(root.begin()+4);
 array<int,9> perm;for(int i=0;i<9;i++)perm[i]=i;
 bool adjacency[9][9]{};for(auto [i,j]:E)adjacency[i][j]=adjacency[j][i]=true;
 do {bool ok=perm[4]==4;for(int i=0;i<9;i++)for(int j=0;j<9;j++)if(adjacency[i][j]!=adjacency[perm[i]][perm[j]])ok=false;if(ok)autos.push_back(perm);}while(next_permutation(perm.begin(),perm.end()));
 cerr<<"automorphisms="<<autos.size()<<"\n";if(autos.size()>12)return 4;
 for(int g=0;g<(int)autos.size();g++){for(int i=0;i<3;i++)signals[i].acts[g]=i;for(int i=0;i<9;i++)signals[raw[i]].acts[g]=raw[autos[g][i]];}
 started=chrono::steady_clock::now();bool ans=search(root,maxk,initialt);double elapsed=chrono::duration<double>(chrono::steady_clock::now()-started).count();
 cout<<"result="<<(stopped?"UNKNOWN":ans?"FOUND":"EXCLUDED")<<" k="<<maxk<<" t="<<initialt<<" sec="<<elapsed<<" nodes="<<nodes<<" hits="<<hits<<" branches="<<branches<<" failed="<<failed.size()<<" signals="<<signals.size()<<" bins="<<bins.size()<<"\n";
 for(int i=0;i<32;i++)if(depths[i])cout<<"depth "<<i<<" nodes "<<depths[i]<<"\n";
}
