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
using namespace std;
constexpr int N=17,G=28,W=2;
struct Gate {int op,a,b;};
using Circuit=array<Gate,G>;
using Bits=array<uint64_t,W>;
struct KeyHash {size_t operator()(const Bits& b)const{return b[0]^(b[1]*0x9e3779b97f4a7c15ULL);}};
array<Bits,N> inputs;Bits target{},singleton_mask{};
vector<vector<Gate>> seeds;
mt19937_64 rng;
int ri(int n){return rng()%n;}
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
  bool star=(g.a<6&&!(support[g.b]&63))||(g.b<6&&!(support[g.a]&63))||
   (g.a>=6&&g.a<N&&support[g.b]<64)||(g.b>=6&&g.b<N&&support[g.a]<64);
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
Circuit seed(){
 auto c=seeds[ri(seeds.size())];
 while(c.size()>G){
  vector<int> choices;bool any=ri(8)==0;
  for(int i=0;i<(int)c.size()-1;i++)if(any||c[i].op==1)choices.push_back(i);
  int del=choices[ri(choices.size())],rep=ri(2)?c[del].a:c[del].b;
  for(auto& g:c)for(int* x:{&g.a,&g.b}){if(*x==N+del)*x=rep;else if(*x>N+del)--*x;}
  c.erase(c.begin()+del);
 }
 Circuit out;copy(c.begin(),c.end(),out.begin());return prune(out);
}
void dump(const Circuit& c,const string& path){ofstream f(path);f<<"[\n";for(int k=0;k<G;k++){auto g=c[k];f<<"["<<g.op<<","<<g.a<<","<<g.b<<"]"<<(k+1<G?",":"")<<"\n";}f<<"]\n";}
int main(int argc,char**argv){
 if(argc!=6){cerr<<"usage: search_fixed tests.txt seeds.txt seconds seed prefix\n";return 2;}
 ifstream f(argv[1]);int m;f>>m;assert(m<=64*W);
 for(int j=0;j<m;j++){uint32_t x;int y;f>>x>>y;for(int i=0;i<N;i++)if(x>>i&1)inputs[i][j/64]|=uint64_t(1)<<(j%64);if(y)target[j/64]|=uint64_t(1)<<(j%64);}
 if(m==93)for(int j=76;j<93;j++)singleton_mask[j/64]|=uint64_t(1)<<(j%64);
 ifstream s(argv[2]);int count;s>>count;while(count--){int n;s>>n;vector<Gate> gs(n);for(auto& g:gs)s>>g.op>>g.a>>g.b;seeds.push_back(gs);}
 int duration=stoi(argv[3]);rng.seed(stoull(argv[4]));string prefix=argv[5];
 vector<Circuit> pool;vector<Bits> keys;vector<int> kinds;array<int,128> populations{};unordered_map<Bits,int,KeyHash> index;
 auto tag=[](Bits b,int kind){b[1]|=uint64_t(kind)<<56;return b;};
 auto remember=[&](const Circuit& c,Bits b){
  auto [mi,wr]=errors(b);if(mi>8||wr>52||mi+wr>56||singletons(b))return;auto [ac,mixed]=features(c);int kind=8*min(ac,9)+4*(mixed>0)+2*(wr>0)+(mi==0);Bits key=tag(b,kind);
  auto it=index.find(key);if(it!=index.end()){if(ri(4)==0)pool[it->second]=c;return;}
  if(pool.size()<512){index[key]=pool.size();pool.push_back(c);keys.push_back(b);kinds.push_back(kind);populations[kind]++;}
  else{int q=ri(pool.size());auto old=errors(keys[q]);if(populations[kind]<populations[kinds[q]]||(kind==kinds[q]&&mi*3+wr<=old.first*3+old.second)){
   index.erase(tag(keys[q],kinds[q]));populations[kinds[q]]--;index[key]=q;pool[q]=c;keys[q]=b;kinds[q]=kind;populations[kind]++;
  }}
 };
 auto savepool=[&](){ofstream f(prefix+"-pool.json");f<<"[\n";for(int i=0;i<(int)pool.size();i++){auto [mi,wr]=errors(keys[i]);auto [ac,mx]=features(pool[i]);f<<"{\"miss\":"<<mi<<",\"false\":"<<wr<<",\"active_and\":"<<ac<<",\"mixed_and\":"<<mx<<",\"gates\":[";for(int k=0;k<G;k++){auto g=pool[i][k];f<<"["<<g.op<<","<<g.a<<","<<g.b<<"]"<<(k+1<G?",":"");}f<<"]}"<<(i+1<(int)pool.size()?",":"")<<"\n";}f<<"]\n";};
 Circuit current=seed();Bits sig=values(current)[N+G-1];auto [miss,wrong]=errors(sig);int best=100000;
 remember(current,sig);
 long long iterations=0,restarts=0;int report=-1;auto begin=chrono::steady_clock::now();
 while(true){
  double elapsed=chrono::duration<double>(chrono::steady_clock::now()-begin).count();if(elapsed>=duration)break;
  if((int)elapsed/10>report){report=(int)elapsed/10;cout<<"seconds "<<elapsed<<" iterations "<<iterations<<" restarts "<<restarts<<" best "<<best<<" current miss "<<miss<<" false "<<wrong<<" pool "<<pool.size()<<endl;if(report%3==0)savepool();}
  int phase=(iterations/500000)%30;int weights[]={1,2,4,8,16,32};int weight=weights[(phase/5)%6];double temps[]={0.0,0.25,0.8,1.5,3.0};double temp=temps[phase%5];
  Circuit next=current;int mutations=1+(ri(4)==0)+(ri(12)==0);
  for(int k=0;k<mutations;k++){int j=ri(G),mode=ri(12);if(mode<5)next[j].a=ri(N+j);else if(mode<10)next[j].b=ri(N+j);else next[j].op^=1;}
  Bits nextsig=values(next)[N+G-1];auto [nm,nw]=errors(nextsig);int ns=nm*weight+nw,score=miss*weight+wrong;
  score+=10000*singletons(sig);ns+=10000*singletons(nextsig);
  if(phase%2){score+=2*weight*(wrong==0&&miss>0);ns+=2*weight*(nw==0&&nm>0);}
  if(nm*3+nw<best){best=nm*3+nw;dump(next,prefix+"-best.json");cout<<"BEST "<<best<<" miss "<<nm<<" false "<<nw<<" at "<<elapsed<<endl;}
  if(nm==0&&nw==0){dump(next,prefix+"-solution.json");savepool();cout<<"SOLUTION "<<prefix<<"-solution.json"<<endl;return 0;}
  if(ns<=score||(temp>0&&uniform_real_distribution<double>(0,1)(rng)<exp((score-ns)/temp))){bool changed=nextsig!=sig;current=next;sig=nextsig;miss=nm;wrong=nw;if(iterations%4096==0||(nm==0&&changed))remember(current,sig);}
  iterations++;
  if(iterations%100000==0){current=prune(current);sig=values(current)[N+G-1];auto e=errors(sig);miss=e.first;wrong=e.second;remember(current,sig);if(miss==0&&wrong==0){dump(current,prefix+"-solution.json");savepool();cout<<"SOLUTION after pruning"<<endl;return 0;}}
  if(iterations%30000000==0){current=(!pool.empty()&&ri(2))?pool[ri(pool.size())]:seed();sig=values(current)[N+G-1];auto e=errors(sig);miss=e.first;wrong=e.second;remember(current,sig);restarts++;}
 }
 savepool();cout<<"DONE iterations "<<iterations<<" best "<<best<<" pool "<<pool.size()<<endl;
}
