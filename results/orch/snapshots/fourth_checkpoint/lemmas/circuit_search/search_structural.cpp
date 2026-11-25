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
#include <unordered_map>
#include <cassert>
#include <functional>
using namespace std;
#ifndef INPUTS
#define INPUTS 26
#endif
#ifndef GATES
#define GATES 63
#endif
#ifndef WORDS
#define WORDS 13
#endif
#ifndef POINTS
#define POINTS 13
#endif
#ifndef MAX_MISS
#define MAX_MISS 16
#endif
#ifndef MAX_WRONG
#define MAX_WRONG 704
#endif
constexpr int N=INPUTS,G=GATES,W=WORDS;
struct Gate {int op,a,b;};
using Circuit=array<Gate,G>;
using Bits=array<uint64_t,W>;
using PoolKey=array<uint64_t,W+1>;
struct KeyHash {size_t operator()(const PoolKey& b)const{size_t h=0;for(auto x:b)h=(h^x)*0x9e3779b97f4a7c15ULL;return h;}};
array<Bits,N> inputs;Bits target{},singleton_mask{};
vector<vector<Gate>> seeds;
mt19937_64 rng;
int ri(int n){return rng()%n;}
void reload_seeds(const string& path){
 ifstream s(path);int count;s>>count;assert(s&&count>0);vector<vector<Gate>> fresh;
 while(count--){int n;s>>n;assert(n>0);vector<Gate> gs(n);for(int j=0;j<n;j++){auto&g=gs[j];s>>g.op>>g.a>>g.b;assert(s&&(g.op==0||g.op==1)&&g.a>=0&&g.a<N+j&&g.b>=0&&g.b<N+j);}fresh.push_back(gs);}
 seeds.swap(fresh);
}
auto values(const Circuit& c){
 array<Bits,N+G> v;copy(inputs.begin(),inputs.end(),v.begin());
 for(int k=0;k<G;k++){auto g=c[k];for(int j=0;j<W;j++)v[N+k][j]=g.op?(v[g.a][j]|v[g.b][j]):(v[g.a][j]&v[g.b][j]);}
 return v;
}
pair<int,int> errors(Bits b){int miss=0,wrong=0;for(int j=0;j<W;j++){miss+=popcount(target[j]&~b[j]);wrong+=popcount(~target[j]&b[j]);}return{miss,wrong};}
int singletons(Bits b){int out=0;for(int j=0;j<W;j++)out+=popcount(b[j]&singleton_mask[j]);return out;}
pair<int,int> features(const Circuit& c){
 array<bool,N+G> used{};used[N+G-1]=true;
 for(int k=G-1;k>=0;k--)if(used[N+k])used[c[k].a]=used[c[k].b]=true;
 array<uint32_t,N+G> support;for(int i=0;i<N;i++)support[i]=uint32_t(1)<<i;
 int ac=0,mixed=0;
 for(int k=0;k<G;k++){auto g=c[k];support[N+k]=support[g.a]|support[g.b];if(used[N+k]&&g.op==0){ac++;
  constexpr uint32_t pmask=(uint32_t(1)<<POINTS)-1;
  bool star=(g.a<POINTS&&!(support[g.b]&pmask))||(g.b<POINTS&&!(support[g.a]&pmask))||
   (g.a>=POINTS&&g.a<N&&support[g.b]<=pmask)||(g.b>=POINTS&&g.b<N&&support[g.a]<=pmask);
  mixed+=!star;
 }}return{ac,mixed};
}
Circuit prune(const Circuit& c){
 auto v=values(c);array<int,N+G> repl;array<Gate,G> updated;
 for(int i=0;i<N;i++)repl[i]=i;
 for(int i=N;i<N+G;i++){
  int chosen=-2,quality=-100000;
  for(int j=0;j<i;j++){
   bool ok=true;int q=0;
   for(int w=0;w<W;w++){ok &= (v[i][w]&~v[j][w]&target[w])==0 && (v[j][w]&~v[i][w]&~target[w])==0;q+=100*popcount(v[j][w]&target[w])-popcount(v[j][w]&~target[w]);}
   if(ok&&q>quality){chosen=repl[j];quality=q;}
  }
  if(chosen==-2){
   bool zero=true;for(int w=0;w<W;w++)zero &= (v[i][w]&target[w])==0;
   if(zero)chosen=-1;
  }
  auto g=c[i-N];int a=repl[g.a],b=repl[g.b];
  if(chosen==-2){
   if(a==b)chosen=a;
   else if(a==-1||b==-1)chosen=g.op?(a==-1?b:a):-1;
   else{chosen=i;updated[i-N]={g.op,a,b};}
  }
  repl[i]=chosen;
 }
 int output=repl[N+G-1];if(output<0)return c;
 array<bool,N+G> used{};used[output]=true;
 for(int i=G-1;i>=0;i--)if(used[N+i]){used[updated[i].a]=used[updated[i].b]=true;}
 array<int,N+G> ren;for(int i=0;i<N;i++)ren[i]=i;
 Circuit result;int count=0;
 for(int i=0;i<G;i++)if(used[N+i]){auto g=updated[i];ren[N+i]=N+count;result[count++]={g.op,ren[g.a],ren[g.b]};}
 output=ren[output];
 while(count<G){result[count]={1,output,output};output=N+count++;}
 auto old=v[N+G-1],now=values(result)[N+G-1];
 for(int w=0;w<W;w++){assert((old[w]&~now[w]&target[w])==0);assert((now[w]&~old[w]&~target[w])==0);}
 return result;
}
Circuit seed(int forced=-1){
 auto c=seeds[forced<0?ri(seeds.size()):forced];
 while(c.size()>G){
  vector<int> choices;bool any=ri(8)==0;
  for(int i=0;i<(int)c.size()-1;i++)if(any||c[i].op==1)choices.push_back(i);
  int del=choices[ri(choices.size())],rep=ri(2)?c[del].a:c[del].b;
  for(auto& g:c)for(int* x:{&g.a,&g.b}){if(*x==N+del)*x=rep;else if(*x>N+del)--*x;}
  c.erase(c.begin()+del);
 }
 while(c.size()<G){int output=N+c.size()-1;c.push_back({0,output,output});}
 Circuit out;copy(c.begin(),c.end(),out.begin());return prune(out);
}
void dump(const Circuit& c,const string& path){ofstream f(path);f<<"[\n";for(int k=0;k<G;k++){auto g=c[k];f<<"["<<g.op<<","<<g.a<<","<<g.b<<"]"<<(k+1<G?",":"")<<"\n";}f<<"]\n";}
Circuit rewrite(const Circuit& current){
 array<bool,N+G> active{};active[N+G-1]=true;
 for(int k=G-1;k>=0;k--)if(active[N+k])active[current[k].a]=active[current[k].b]=true;
 vector<int> choices;for(int k=0;k<G;k++)if(active[N+k])choices.push_back(k);
 int chosen=choices[ri(choices.size())],mode=ri(4);
 vector<Gate> made;unordered_map<uint64_t,int> cache;array<int,N+G> memo;memo.fill(-1);
 auto emit=[&](int op,int a,int b){
  if(a==b)return a;if(a>b)swap(a,b);
  uint64_t key=(uint64_t(op)<<48)|(uint64_t(a)<<24)|uint64_t(b);
  auto found=cache.find(key);if(found!=cache.end())return found->second;
  int output=N+made.size();cache[key]=output;made.push_back({op,a,b});return output;
 };
 function<int(int)> build=[&](int wire)->int{
  if(wire<N)return wire;if(memo[wire]>=0)return memo[wire];
  int k=wire-N;auto g=current[k];int result=-1;
  if(k==chosen){
   if(mode==0||mode==1){
    int child=ri(2)?g.a:g.b,other=(child==g.a?g.b:g.a);
    if(child>=N){auto sub=current[child-N];
     if((mode==0&&sub.op!=g.op)||(mode==1&&sub.op==g.op)){
      int a=build(sub.a),b=build(sub.b),w=build(other);
      if(mode==0)result=emit(sub.op,emit(g.op,a,w),emit(g.op,b,w));
      else result=emit(g.op,a,emit(g.op,b,w));
     }
    }
   }else if(mode==2&&g.a>=N&&g.b>=N){
    auto x=current[g.a-N],y=current[g.b-N];
    if(x.op==y.op&&x.op!=g.op){
     int common=-1,left=-1,right=-1;
     for(int a:{x.a,x.b})for(int b:{y.a,y.b})if(a==b){common=a;left=(a==x.a?x.b:x.a);right=(b==y.a?y.b:y.a);}
     if(common>=0)result=emit(x.op,build(common),emit(g.op,build(left),build(right)));
    }
   }else if(mode==3){
    // Inverse absorption temporarily introduces a reusable mixed intermediate.
    int value=emit(g.op,build(g.a),build(g.b)),extra=build(ri(wire));
    int outer=ri(2);result=emit(outer,value,emit(1-outer,value,extra));
   }
  }
  if(result<0)result=emit(g.op,build(g.a),build(g.b));
  return memo[wire]=result;
 };
 int output=build(N+G-1);vector<bool> used(N+made.size());used[output]=true;
 for(int k=(int)made.size()-1;k>=0;k--)if(used[N+k])used[made[k].a]=used[made[k].b]=true;
 vector<int> ren(N+made.size());for(int i=0;i<N;i++)ren[i]=i;
 Circuit next;int count=0;
 for(int k=0;k<(int)made.size();k++)if(used[N+k]){
  if(count==G)return current;auto g=made[k];ren[N+k]=N+count;next[count++]={g.op,ren[g.a],ren[g.b]};
 }
 output=ren[output];while(count<G){next[count]={1,output,output};output=N+count++;}
 assert(values(current)[N+G-1]==values(next)[N+G-1]);
 return next;
}
int main(int argc,char**argv){
 if(argc==5&&string(argv[1])=="--rewrite-file"){
  rng.seed(stoull(argv[4]));for(auto&v:inputs)for(auto&w:v)w=rng();reload_seeds(argv[2]);
  assert(seeds.front().size()<=G);Circuit c;int count=0;for(auto g:seeds.front())c[count++]=g;
  while(count<G){int out=N+count-1;c[count++]={1,out,out};}
  for(int j=0;j<500;j++)c=rewrite(c);dump(c,argv[3]);cout<<"Wrote 500-rewrite fixture"<<endl;return 0;
 }
 if(argc==2&&string(argv[1])=="--selftest"){
  rng.seed(65043);for(auto&v:inputs)for(auto&w:v)w=rng();int changes=0;
  for(int trial=0;trial<20000;trial++){
   Circuit c;for(int k=0;k<G;k++)c[k]={ri(2),ri(N+k),ri(N+k)};
   if(trial%2==0){int a=ri(N),b=ri(N),d=ri(N),op=ri(2);c[G-3]={op,a,b};c[G-2]={op,a,d};c[G-1]={1-op,N+G-3,N+G-2};}
   auto before=values(c)[N+G-1];for(int j=0;j<5;j++)c=rewrite(c);assert(before==values(c)[N+G-1]);changes+=1;
  }
  cout<<"PASS structural rewrite random/signature checks "<<changes<<" circuits, five rewrites each"<<endl;return 0;
 }
 if(argc!=6){cerr<<"usage: search_fixed tests.txt seeds.txt seconds seed prefix\n";return 2;}
 ifstream f(argv[1]);int m;f>>m;assert(m<=64*W);
 constexpr uint32_t pmask=(uint32_t(1)<<POINTS)-1,lmask=((uint32_t(1)<<N)-1)^pmask;
 uint32_t singleton_inputs=0;bool saw_point_side=false,saw_line_side=false;
 for(int j=0;j<m;j++){uint32_t x;int y;f>>x>>y;for(int i=0;i<N;i++)if(x>>i&1)inputs[i][j/64]|=uint64_t(1)<<(j%64);if(y)target[j/64]|=uint64_t(1)<<(j%64);
  assert(x<(uint32_t(1)<<N)&&(y==0||y==1));if(popcount(x)==1)singleton_inputs|=x;saw_point_side|=x==pmask;saw_line_side|=x==lmask;
  if(popcount(x)==1||x==pmask||x==lmask){assert(y==0);singleton_mask[j/64]|=uint64_t(1)<<(j%64);}
 }
 assert(singleton_inputs==(pmask|lmask)&&saw_point_side&&saw_line_side);
 reload_seeds(argv[2]);
 int duration=stoi(argv[3]);rng.seed(stoull(argv[4]));string prefix=argv[5];
 vector<Circuit> pool;vector<Bits> keys;vector<int> kinds;array<int,256> populations{};unordered_map<PoolKey,int,KeyHash> index;
 auto tag=[](Bits b,int kind){PoolKey key;copy(b.begin(),b.end(),key.begin());key[W]=kind;return key;};
 auto remember=[&](const Circuit& c,Bits b){
  auto [mi,wr]=errors(b);if(mi>MAX_MISS||wr>MAX_WRONG||singletons(b))return;auto [ac,mixed]=features(c);int kind=8*min(ac,31)+4*(mixed>0)+2*(wr>0)+(mi==0);PoolKey key=tag(b,kind);
  auto it=index.find(key);if(it!=index.end()){if(ri(4)==0)pool[it->second]=c;return;}
  if(pool.size()<512){index[key]=pool.size();pool.push_back(c);keys.push_back(b);kinds.push_back(kind);populations[kind]++;}
  else{int q=ri(pool.size());auto old=errors(keys[q]);if(populations[kind]<populations[kinds[q]]||(kind==kinds[q]&&mi*3+wr<=old.first*3+old.second)){
   index.erase(tag(keys[q],kinds[q]));populations[kinds[q]]--;index[key]=q;pool[q]=c;keys[q]=b;kinds[q]=kind;populations[kind]++;
  }}
 };
 auto savepool=[&](){ofstream f(prefix+"-pool.json");f<<"[\n";for(int i=0;i<(int)pool.size();i++){auto [mi,wr]=errors(keys[i]);auto [ac,mx]=features(pool[i]);f<<"{\"miss\":"<<mi<<",\"false\":"<<wr<<",\"active_and\":"<<ac<<",\"mixed_and\":"<<mx<<",\"gates\":[";for(int k=0;k<G;k++){auto g=pool[i][k];f<<"["<<g.op<<","<<g.a<<","<<g.b<<"]"<<(k+1<G?",":"");}f<<"]}"<<(i+1<(int)pool.size()?",":"")<<"\n";}f<<"]\n";};
 Circuit current=seed(0);Bits sig=values(current)[N+G-1];auto [miss,wrong]=errors(sig);int best=100000,best_all_positive=100000;
 if(miss==0&&singletons(sig)==0){best_all_positive=wrong;dump(current,prefix+"-all-positive.json");cout<<"ALLPOS initial false "<<wrong<<endl;}
 remember(current,sig);
 long long iterations=0,restarts=0;int report=-1;auto begin=chrono::steady_clock::now();
 while(true){
  double elapsed=chrono::duration<double>(chrono::steady_clock::now()-begin).count();if(elapsed>=duration)break;
  if((int)elapsed/10>report){report=(int)elapsed/10;cout<<"seconds "<<elapsed<<" iterations "<<iterations<<" restarts "<<restarts<<" best "<<best<<" current miss "<<miss<<" false "<<wrong<<" pool "<<pool.size()<<endl;if(report%3==0)savepool();}
  int phase=(iterations/500000)%30;
  array<int,6> weights=N>17?array<int,6>{1,4,16,64,256,1024}:array<int,6>{1,2,4,8,16,32};
  array<double,5> temps=N>17?array<double,5>{0.0,1.0,4.0,12.0,40.0}:array<double,5>{0.0,0.25,0.8,1.5,3.0};
  int weight=weights[(phase/5)%6];double temp=temps[phase%5];
  Circuit next=current;
  if(ri(1000)==0)next=rewrite(current);
  else{int mutations=1+(ri(4)==0)+(ri(12)==0);
   for(int k=0;k<mutations;k++){int j=ri(G),mode=ri(12);if(mode<5)next[j].a=ri(N+j);else if(mode<10)next[j].b=ri(N+j);else next[j].op^=1;}}
  Bits nextsig=values(next)[N+G-1];auto [nm,nw]=errors(nextsig);int ns=nm*weight+nw,score=miss*weight+wrong;
  score+=1000000*singletons(sig);ns+=1000000*singletons(nextsig);
  if(phase%2){score+=2*weight*(wrong==0&&miss>0);ns+=2*weight*(nw==0&&nm>0);}
  if(nm*3+nw<best&&singletons(nextsig)==0){best=nm*3+nw;dump(next,prefix+"-best.json");cout<<"BEST "<<best<<" miss "<<nm<<" false "<<nw<<" at "<<elapsed<<endl;}
  if(nm==0&&singletons(nextsig)==0&&nw<best_all_positive){best_all_positive=nw;dump(next,prefix+"-all-positive.json");cout<<"ALLPOS false "<<nw<<" at "<<elapsed<<endl;}
  if(nm==0&&nw==0){dump(next,prefix+"-solution.json");savepool();cout<<"SOLUTION "<<prefix<<"-solution.json"<<endl;return 0;}
  if(ns<=score||(temp>0&&uniform_real_distribution<double>(0,1)(rng)<exp((score-ns)/temp))){bool changed=nextsig!=sig;current=next;sig=nextsig;miss=nm;wrong=nw;if(iterations%4096==0||(nm==0&&changed))remember(current,sig);}
  iterations++;
  if(iterations%1000000==0){current=prune(current);sig=values(current)[N+G-1];auto e=errors(sig);miss=e.first;wrong=e.second;remember(current,sig);if(miss==0&&singletons(sig)==0&&wrong<best_all_positive){best_all_positive=wrong;dump(current,prefix+"-all-positive.json");cout<<"ALLPOS after pruning false "<<wrong<<endl;}if(miss==0&&wrong==0){dump(current,prefix+"-solution.json");savepool();cout<<"SOLUTION after pruning"<<endl;return 0;}}
  if(iterations%30000000==0){reload_seeds(argv[2]);current=(!pool.empty()&&ri(2))?pool[ri(pool.size())]:seed();sig=values(current)[N+G-1];auto e=errors(sig);miss=e.first;wrong=e.second;remember(current,sig);restarts++;}
 }
 savepool();cout<<"DONE iterations "<<iterations<<" best "<<best<<" pool "<<pool.size()<<endl;
}
