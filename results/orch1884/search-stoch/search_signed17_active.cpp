#include <array>
#include <vector>
#include <random>
#include <chrono>
#include <iostream>
#include <algorithm>
#include <csignal>
#include <string>
using namespace std;
using Word=unsigned long long;
using Bits=array<Word,16>;
constexpr int V=10,N=17,B=10,OUTPUT=B+N-1;
struct Gate{int op,a,b;};
using Circuit=array<Gate,N>;
using Values=array<Bits,B+N>;
mt19937 rng;
volatile sig_atomic_t stopFlag=0;
void stopped(int){stopFlag=1;}
array<Bits,B>inputs{};
Bits target{};
vector<pair<int,int>>edges={{0,1},{1,2},{2,3},{3,4},{4,0},{0,5},{1,6},{2,7},{3,8},{4,9},{5,7},{7,9},{9,6},{6,8},{8,5}};
vector<int>covers;
array<array<bool,V>,V>adj{};
int firstOrbit=-1;
Word operation(int op,Word a,Word b){return op==0?(a&b):op==1?(a|b):op==2?(a&~b):(~a&b);}
Values values(const Circuit&c){Values w{};for(int i=0;i<B;i++)w[i]=inputs[i];for(int i=0;i<N;i++){auto g=c[i];for(int k=0;k<16;k++)w[B+i][k]=operation(g.op,w[g.a][k],w[g.b][k]);}return w;}
int rawScore(const Circuit&c){auto w=values(c);int n=0;for(int k=0;k<16;k++){Word bad=w[OUTPUT][k]^target[k];n+=__builtin_popcountll(bad)+3*__builtin_popcountll(bad&~target[k]);}return n;}
bool activeMixed(const Circuit&c){array<bool,B+N>used{};used[OUTPUT]=true;bool mixed=false;for(int i=N-1;i>=0;i--)if(used[B+i]){auto g=c[i];mixed|=g.op>=2;used[g.a]=true;used[g.b]=true;}return mixed;}
int score(const Circuit&c){return rawScore(c)+(activeMixed(c)?0:8);}
Bits forceOutput(const Circuit&c,Values w,int i,Word v){w[B+i].fill(v);for(int j=i+1;j<N;j++){auto g=c[j];for(int k=0;k<16;k++)w[B+j][k]=operation(g.op,w[g.a][k],w[g.b][k]);}return w[OUTPUT];}
int coordinate(Circuit&c,int i,int temp){
 auto w=values(c);Bits f0=forceOutput(c,w,i,0),f1=forceOutput(c,w,i,~0ULL),care{},want{};
 for(int k=0;k<16;k++){care[k]=f0[k]^f1[k];want[k]=target[k]^f0[k];}
 int best=1000000,count=0;Gate keep=c[i];
 for(int op=0;op<4;op++)for(int a=0;a<B+i;a++)for(int b=0;b<=a;b++){
  int err=0;bool nonzero=false,different=false;for(int k=0;k<16;k++){Word value=operation(op,w[a][k],w[b][k]);nonzero|=value!=0;different|=value!=w[op==2?a:b][k];Word bad=(value^want[k])&care[k];err+=__builtin_popcountll(bad)+3*__builtin_popcountll(bad&~target[k]);}
  if(op>=2&&(!nonzero||!different))continue;
  Gate old=c[i];c[i]={op,a,b};int penalty=activeMixed(c)?0:8;c[i]=old;
  int sc=err+penalty+(temp?int(rng()%(temp+1)):0);
  if(sc<best){best=sc;count=1;keep={op,a,b};}else if(sc==best&&rng()%++count==0)keep={op,a,b};
 }
 c[i]=keep;return score(c);
}
bool extendAut(array<int,V>&p,array<bool,V>&used){
 int i=-1,quality=-1;
 for(int u=0;u<V;u++)if(p[u]<0){int q=0;for(int j=0;j<V;j++)q+=p[j]>=0&&adj[u][j];if(q>quality){quality=q;i=u;}}
 if(i<0)return true;
 for(int a=0;a<V;a++)if(!used[a]){
  bool valid=true;for(int j=0;j<V;j++)if(p[j]>=0&&adj[i][j]!=adj[a][p[j]])valid=false;
  if(!valid)continue;p[i]=a;used[a]=true;if(extendAut(p,used))return true;used[a]=false;p[i]=-1;
 }
 return false;
}
array<int,V>automorphism(int a,int imageA,int b=-1,int imageB=-1){
 array<int,V>p;p.fill(-1);array<bool,V>used{};p[a]=imageA;used[imageA]=true;
 if(b>=0){p[b]=imageB;used[imageB]=true;}
 if(!extendAut(p,used)){cerr<<"FAULT automorphism"<<endl;exit(2);}return p;
}
Circuit seed(){
 int cover=covers[rng()%covers.size()];array<vector<int>,V>star;
 vector<int>order(15);for(int i=0;i<15;i++)order[i]=i;shuffle(order.begin(),order.end(),rng);int lost=(1<<order[0])|(1<<order[1])|(1<<order[2]);
 for(int ei=0;ei<15;ei++){if(lost>>ei&1)continue;auto[a,b]=edges[ei];if((cover>>a&1)&&(cover>>b&1)){if(rng()%2)swap(a,b);}else if(!(cover>>a&1))swap(a,b);star[a].push_back(b);}
 vector<int>centers;for(int v=0;v<V;v++)if(!star[v].empty())centers.push_back(v);shuffle(centers.begin(),centers.end(),rng);
 vector<Gate>g;vector<int>roots;
 for(int v:centers){shuffle(star[v].begin(),star[v].end(),rng);int cur=star[v][0];for(size_t j=1;j<star[v].size();j++){g.push_back({1,cur,star[v][j]});cur=B+g.size()-1;}g.push_back({0,v,cur});roots.push_back(B+g.size()-1);}
 shuffle(roots.begin(),roots.end(),rng);int cur=roots[0];for(size_t j=1;j<roots.size();j++){g.push_back({1,cur,roots[j]});cur=B+g.size()-1;}
 int k=-1;for(size_t i=0;i<g.size();i++)if(g[i].op==1&&g[i].a<V&&g[i].b<V&&g[i].a!=g[i].b){k=i;break;}
 if(k<0||g.size()>N){cerr<<"FAULT seed"<<endl;exit(2);}
 Gate front=g[k];g.erase(g.begin()+k);g.insert(g.begin(),front);
 for(auto&h:g)for(int*p:{&h.a,&h.b}){if(*p==B+k)*p=B;else if(*p>=B&&*p<B+k)++*p;}
 auto perm=automorphism(g[0].a,0,g[0].b,adj[g[0].a][g[0].b]?1:2);
 for(auto&h:g)for(int*p:{&h.a,&h.b})if(*p<V)*p=perm[*p];
 while(g.size()<N){int last=B+g.size()-1;g.push_back({0,last,last});}
 Circuit c;copy(g.begin(),g.end(),c.begin());bool edge=firstOrbit<0?rng()%2:firstOrbit==0;c[0]={1,0,edge?1:2};return c;
}
void reorder(Circuit&c){int i=1+rng()%(N-3);auto h=c[i+1];if(h.a==B+i||h.b==B+i)return;swap(c[i],c[i+1]);for(int j=i+2;j<N;j++)for(int*p:{&c[j].a,&c[j].b}){if(*p==B+i)++*p;else if(*p==B+i+1)--*p;}}
void show(const Circuit&c,int s,long long trial){cout<<"best "<<s<<" trial "<<trial<<" gates [";for(auto g:c)cout<<"("<<g.op<<","<<g.a<<","<<g.b<<"),";cout<<"]"<<endl;}
struct PhaseResult{int count;unsigned phase;int freeInput;array<bool,B+N>live;int binary;};
PhaseResult phaseOpt(const Circuit&c){
 array<bool,B+N>live{};live[OUTPUT]=true;int binary=0;for(int i=N-1;i>=0;i--)if(live[B+i]){binary++;live[c[i].a]=true;live[c[i].b]=true;}
 int best=100,freeInput=0;unsigned keep=0;
 for(unsigned p=0;p<(1u<<N);p++){
  unsigned bad=(p>>(N-1)&1)?(1u<<OUTPUT):0;
  for(int i=0;i<N;i++)if(live[B+i]){auto g=c[i];int out=p>>i&1,pa=g.a<B?0:(p>>(g.a-B)&1),pb=g.b<B?0:(p>>(g.b-B)&1);if(pa^out^(g.op==3))bad|=1u<<g.a;if(pb^out^(g.op==2))bad|=1u<<g.b;}
  unsigned prim=bad&((1u<<V)-1);int n=__builtin_popcount(bad)-bool(prim);
  if(n<best){best=n;keep=p;freeInput=prim?__builtin_ctz(prim):0;if(best==0)break;}
 }
 return {best,keep,freeInput,live,binary};
}
struct Realization{vector<Gate>gates;int output;array<int,V>perm;};
Realization realize(const Circuit&c,const PhaseResult&r){
 array<int,B+N>pos,neg;pos.fill(-1);neg.fill(-1);auto perm=automorphism(r.freeInput,0);
 for(int i=0;i<V;i++)pos[i]=perm[i];neg[r.freeInput]=10;
 vector<Gate>out;
 auto add=[&](int op,int a,int b){int ix=11+out.size();out.push_back({op,a,b});return ix;};
 auto complement=[&](int s){if(neg[s]<0)neg[s]=add(2,pos[s],pos[s]);return neg[s];};
 for(int i=0;i<N;i++)if(r.live[B+i]){
  auto g=c[i];int phase=r.phase>>i&1,pa=g.a<B?0:(r.phase>>(g.a-B)&1),pb=g.b<B?0:(r.phase>>(g.b-B)&1);
  int a=(pa^phase^(g.op==3))?complement(g.a):pos[g.a];
  int b=(pb^phase^(g.op==2))?complement(g.b):pos[g.b];
  pos[B+i]=add(phase^(g.op==1),a,b);
 }
 int output=(r.phase>>(N-1)&1)?complement(OUTPUT):pos[OUTPUT];
 if(int(out.size())!=r.binary+r.count){cerr<<"FAULT phase count"<<endl;exit(2);}
 return {out,output,perm};
}
void validateRealization(const Circuit&c,const Realization&r,bool requireTarget){
 for(int x=0;x<1024;x++){
  array<bool,128>w{};for(int j=0;j<V;j++)w[j]=x>>j&1;w[10]=!w[0];
  for(size_t i=0;i<r.gates.size();i++){auto g=r.gates[i];if(g.a<0||g.b<0||g.a>=11+int(i)||g.b>=11+int(i)){cerr<<"FAULT realized indices"<<endl;exit(2);}w[11+i]=g.op==0?(w[g.a]&&w[g.b]):g.op==1?(w[g.a]||w[g.b]):!w[g.a];}
  array<Word,B+N>v{};for(int j=0;j<V;j++)v[j]=(x>>r.perm[j]&1)?~0ULL:0;for(int i=0;i<N;i++){auto g=c[i];v[B+i]=operation(g.op,v[g.a],v[g.b]);}
  bool want=v[OUTPUT]!=0;if(w[r.output]!=want){cerr<<"FAULT realized semantics"<<endl;exit(2);}
  if(requireTarget){bool targetValue=false;for(auto[a,b]:edges)targetValue|=(x>>a&1)&&(x>>b&1);if(w[r.output]!=targetValue){cerr<<"FAULT target"<<endl;exit(2);}}
 }
}
void printRealization(const Realization&r,const string&label){cout<<label<<" {\"inputs\":11,\"output\":"<<r.output<<",\"gates\":[";for(size_t i=0;i<r.gates.size();i++){if(i)cout<<",";auto g=r.gates[i];cout<<"["<<g.op<<","<<g.a<<","<<g.b<<"]";}cout<<"]}"<<endl;}
void setup(){
 for(auto[a,b]:edges)adj[a][b]=adj[b][a]=true;
 for(int x=0;x<1024;x++){for(int j=0;j<V;j++)if(x>>j&1)inputs[j][x/64]|=1ULL<<(x%64);for(auto[a,b]:edges)if((x>>a&1)&&(x>>b&1)){target[x/64]|=1ULL<<(x%64);break;}}
 for(int c=0;c<1024;c++)if(__builtin_popcount((unsigned)c)==6){bool yes=true;for(auto[a,b]:edges)if(!(c>>a&1)&&!(c>>b&1))yes=false;if(yes)covers.push_back(c);}
}
int main(int argc,char**argv){
 signal(SIGINT,stopped);signal(SIGTERM,stopped);setup();
 if(argc>1&&string(argv[1])=="selftest"){
  rng.seed(188470);for(int t=0;t<32;t++){Circuit c;for(int i=0;i<N;i++)c[i]={int(rng()%4),int(rng()%(B+i)),int(rng()%(B+i))};auto p=phaseOpt(c);auto r=realize(c,p);validateRealization(c,r,false);}
  for(int v=0;v<V;v++){auto p=automorphism(v,0);for(int a=0;a<V;a++)for(int b=0;b<V;b++)if(adj[a][b]!=adj[p[a]][p[b]])return 2;}
  cout<<"SELFTEST_PASS 32 phase realizations on all1024 inputs; all10 free-primary automorphisms"<<endl;return 0;
 }
 rng.seed(argc>1?stoul(argv[1]):188471);int secs=argc>2?stoi(argv[2]):1200;if(argc>3)firstOrbit=stoi(argv[3]);
 auto start=chrono::steady_clock::now();int global=100000,minnot=100;long long trial=0;vector<Circuit>archive;
 for(int run=0;;run++){
  Circuit c=seed();if(!archive.empty()&&rng()%2)c=archive[rng()%archive.size()];int s=score(c),loc=s;Circuit local=c;
  for(int iter=0;iter<6000;iter++,trial++){
   if(trial%1000==0&&(stopFlag||chrono::duration<double>(chrono::steady_clock::now()-start).count()>secs)){cout<<"done "<<trial<<" best "<<global<<" min_paid_not "<<minnot<<endl;return 0;}
   int temp=(iter%400<250)?0:(iter%400<350?16:64);s=coordinate(c,1+rng()%(N-1),temp);
   if(iter%10==0){for(int j=0;j<10;j++)reorder(c);if(score(c)!=s){cerr<<"FAULT reorder"<<endl;return 2;}}
   if(s<loc){local=c;loc=s;}if(s<global){global=s;show(c,rawScore(c),trial);}
   if(rawScore(c)==0&&(minnot==100||trial%1000==0)){
    auto p=phaseOpt(c);if(p.count<minnot){minnot=p.count;cout<<"EXACT_SIGNED binary "<<p.binary<<" paid_NOT "<<p.count<<" free_primary "<<p.freeInput<<" phase "<<p.phase<<" trial "<<trial<<endl;show(c,0,trial);auto r=realize(c,p);validateRealization(c,r,true);printRealization(r,r.gates.size()<=18?"FULL_WITNESS":"REALIZATION");if(r.gates.size()<=18)return 0;}
   }
   if(s<=global+4&&rng()%100==0){if(archive.size()<32)archive.push_back(c);else archive[rng()%archive.size()]=c;}
   if(iter%400==399){c=local;s=loc;}
  }
 }
}
