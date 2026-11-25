#include <array>
#include <vector>
#include <random>
#include <algorithm>
#include <iostream>
#include <fstream>
#include <chrono>
#include <cstdint>
#include <map>
using namespace std;
constexpr int N=14,K=26;
struct G{int op,a,b;};using C=array<G,K>;
array<uint64_t,N> inputs;uint64_t target=0,mask=0;vector<pair<int,int>>edges;vector<int>rows;
mt19937_64 gen(752368912);int rnd(int n){return gen()%n;}
uint64_t evaluate(const C&c){array<uint64_t,N+K>w;copy(inputs.begin(),inputs.end(),w.begin());for(int j=0;j<K;j++){auto g=c[j];w[N+j]=g.op==0?w[g.a]&w[g.b]:w[g.a]|w[g.b];}return w.back();}
int cost(uint64_t v,int wp,int wn){return wp*__builtin_popcountll(v&~target)+wn*__builtin_popcountll(target&~v);}
void dump(const C&c,ostream&o){for(int i=0;i<K;i++)o<<N+i<<" "<<c[i].op<<" "<<c[i].a<<" "<<c[i].b<<"\n";}
int read1count(const C&c){array<uint16_t,N+K>lin{};array<uint32_t,N+K>pairs{};for(int i=0;i<N;i++)lin[i]=1u<<i;for(int j=0;j<K;j++){auto g=c[j];if(g.op==1){lin[N+j]=lin[g.a]|lin[g.b];pairs[N+j]=pairs[g.a]|pairs[g.b];}else for(int e=0;e<(int)edges.size();e++){auto[u,v]=edges[e];if(((lin[g.a]>>u&1)&&(lin[g.b]>>v&1))||((lin[g.a]>>v&1)&&(lin[g.b]>>u&1)))pairs[N+j]|=1u<<e;}}return __builtin_popcount(pairs.back());}
C seed(){
 vector<G>orig;vector<int>terms;vector<int>centres(7);for(int i=0;i<7;i++)centres[i]=i;shuffle(centres.begin(),centres.end(),gen);int side=rnd(2);
 for(int a:centres){int centre=a+7*side;vector<int>ns;for(auto[u,v]:edges)if(!side&&u==centre)ns.push_back(v);else if(side&&v==centre)ns.push_back(u);shuffle(ns.begin(),ns.end(),gen);orig.push_back({1,ns[0],ns[1]});int w=N+orig.size()-1;orig.push_back({1,w,ns[2]});w=N+orig.size()-1;orig.push_back({0,centre,w});terms.push_back(N+orig.size()-1);}
 while(terms.size()>1){int a=rnd(terms.size());int x=terms[a];terms.erase(terms.begin()+a);int b=rnd(terms.size());int y=terms[b];terms.erase(terms.begin()+b);orig.push_back({1,x,y});terms.push_back(N+orig.size()-1);}
 int del=rnd(26),rep=rnd(N+del);C c;int next=0;for(int j=0;j<27;j++)if(j!=del){G g=orig[j];for(int*p:{&g.a,&g.b}){if(*p==N+del)*p=rep;else if(*p>N+del)--*p;}c[next++]=g;}return c;
}
int main(int argc,char**argv){
 if(argc<4){cerr<<"usage: search-fano ROWS EDGES SECONDS\n";return 2;}ifstream rf(argv[1]),ef(argv[2]);int r,a,b;while(rf>>r)rows.push_back(r);while(ef>>a>>b)edges.push_back({a,b});if(rows.size()!=58||edges.size()!=21)return 3;int seconds=atoi(argv[3]);
 for(int ri=0;ri<(int)rows.size();ri++){int r=rows[ri];mask|=1ULL<<ri;for(int i=0;i<N;i++)if(r>>i&1)inputs[i]|=1ULL<<ri;for(auto[u,v]:edges)if((r>>u&1)&&(r>>v&1)){target|=1ULL<<ri;break;}}
 auto start=chrono::steady_clock::now();int best=59;uint64_t steps=0;C bestc;map<uint64_t,C>singleton;
 for(int restart=0;;restart++){
  C c=seed();if(restart%3==2&&!singleton.empty()){auto it=singleton.begin();advance(it,rnd(singleton.size()));c=it->second;int kick=1+rnd(8);while(kick--){int j=rnd(K),m=rnd(5);if(m==0)c[j].op^=1;else if(m<3)c[j].a=rnd(N+j);else c[j].b=rnd(N+j);}}
  int wp=restart%5==0?3:1,wn=restart%5==1?3:1;uint64_t value=evaluate(c);int curr=cost(value,wp,wn),patience=0;
  for(int inner=0;inner<300000;inner++){
   ++steps;C d=c;int edits=1+(rnd(30)==0?1+rnd(3):0);while(edits--){int j=rnd(K),m=rnd(5);if(m==0)d[j].op^=1;else if(m<3)d[j].a=rnd(N+j);else d[j].b=rnd(N+j);}
   uint64_t val=evaluate(d),bad=val^target;int next=cost(val,wp,wn),err=__builtin_popcountll(bad);
   if(next<=curr||(rnd(1000000)<50&&next<=curr+3)){c=d;curr=next;patience=0;}else patience++;
   bool fresh=err==1&&!singleton.count(bad);if(fresh)singleton[bad]=d;
   if(err<best||fresh){if(err<best){best=err;bestc=d;}double secs=chrono::duration<double>(chrono::steady_clock::now()-start).count();cout<<"best "<<best<<" candidate_errors "<<err<<" fp "<<__builtin_popcountll(val&~target)<<" fn "<<__builtin_popcountll(target&~val)<<" read1 "<<read1count(d)<<" seconds "<<secs<<" steps "<<steps<<" restart "<<restart<<endl;string name=err==0?"fano26-heuristic-witness.txt":"fano26-heuristic-best.txt";ofstream f(name);f<<"errors "<<err<<"\n";dump(d,f);if(fresh){ofstream q("fano26-singleton-"+to_string(__builtin_ctzll(bad))+".txt");q<<"errors 1\n";dump(d,q);}if(err==0){dump(d,cout);return 0;}}
   if((steps&65535)==0&&chrono::duration<double>(chrono::steady_clock::now()-start).count()>seconds){cout<<"done best "<<best<<" steps "<<steps<<" singleton_patterns "<<singleton.size()<<endl;return 1;}
   if(patience>80000)break;
  }
 }
}
