#include <cstdio>
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
#ifndef REQUIRE_RAW
#define REQUIRE_RAW 0
#endif
#ifndef OWNER_PRIORITY_WEIGHT
#define OWNER_PRIORITY_WEIGHT 0
#endif
#ifndef MIN_AND
#define MIN_AND POINTS
#endif
#ifndef REQUIRE_NONLINEAR
#define REQUIRE_NONLINEAR 1
#endif
#ifndef RAW_INPUTS
#define RAW_INPUTS INPUTS
#endif
constexpr int N=INPUTS,G=GATES,W=WORDS;
static_assert(OWNER_PRIORITY_WEIGHT>=0);
struct Gate {int op,a,b;};
using Circuit=array<Gate,G>;
using Bits=array<uint64_t,W>;
using PoolKey=array<uint64_t,W+1>;
struct KeyHash {size_t operator()(const PoolKey& b)const{size_t h=0;for(auto x:b)h=(h^x)*0x9e3779b97f4a7c15ULL;return h;}};
array<Bits,N> inputs;Bits target{},singleton_mask{},owner_priority_mask{};
array<Bits,POINTS> owner_positive{};
array<int,POINTS> point_singleton{};
vector<vector<Gate>> seeds;
vector<vector<int>> prefix_groups;
array<vector<pair<int,int>>,N> feature_splits;
long long unfold_attempts=0,unfold_success=0;
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
pair<int,int> errors(Bits b){int miss=0,wrong=0;for(int j=0;j<W;j++){miss+=popcount(target[j]&~b[j]);wrong+=popcount(~target[j]&b[j])+OWNER_PRIORITY_WEIGHT*popcount(owner_priority_mask[j]&b[j]);}return{miss,wrong};}
int singletons(Bits b){int out=0;for(int j=0;j<W;j++)out+=popcount(b[j]&singleton_mask[j]);return out;}
bool large_nonlinear(const Circuit& c){
 auto v=values(c);array<bool,N+G> used{},line{};array<uint64_t,N+G> points{};
 used[N+G-1]=true;for(int k=G-1;k>=0;k--)if(used[N+k])used[c[k].a]=used[c[k].b]=true;
 int and_count=0;for(int k=0;k<G;k++)and_count+=used[N+k]&&c[k].op==0&&c[k].a!=c[k].b;if(and_count<6)return false;
 auto line_sensitive=[&](const Bits& b){for(int p=0;p<POINTS;p++){int j=point_singleton[p];if(b[j/64]>>(j%64)&1)continue;for(int w=0;w<W;w++)if(b[w]&owner_positive[p][w])return true;}return false;};
 for(int i=0;i<N;i++){points[i]=i<POINTS?(uint64_t(1)<<i):0;line[i]=i>=POINTS;}
 for(int k=0;k<G;k++){
  auto g=c[k];points[N+k]=points[g.a]|points[g.b];line[N+k]=line[g.a]||line[g.b];
  if(!used[N+k]||g.op!=0||!line_sensitive(v[g.a])||!line_sensitive(v[g.b])||v[g.a]==v[g.b])continue;
  int owners=0;for(int p=0;p<POINTS;p++){bool live=false;for(int w=0;w<W;w++)live|=(v[N+k][w]&owner_positive[p][w])!=0;owners+=live;}if(owners<4)continue;
  Circuit left=c,right=c;left[k]={1,g.a,g.a};right[k]={1,g.b,g.b};
  if(values(left)[N+G-1]!=v[N+G-1]&&values(right)[N+G-1]!=v[N+G-1])return true;
 }
 return false;
}
bool joint_budget_ok(const Circuit& c){
 if(prefix_groups.empty())return true;
 array<bool,N+G> original_used{};original_used[N+G-1]=true;
 for(int k=G-1;k>=0;k--)if(original_used[N+k])original_used[c[k].a]=original_used[c[k].b]=true;
 int extra=0;for(auto& group:prefix_groups){int count=0;for(int i:group)count+=original_used[i];extra+=max(0,count-1);}
 if(extra==0)return true;
 int original_count=0;for(int k=0;k<G;k++)original_count+=original_used[N+k];
 if(original_count+extra<=G)return true;
 array<int,N+G> ren;for(int i=0;i<N;i++)ren[i]=i;
 vector<Gate> made;unordered_map<uint64_t,int> cache;
 for(int k=0;k<G;k++){
  auto g=c[k];int a=ren[g.a],b=ren[g.b];if(a>b)swap(a,b);
  if(a==b){ren[N+k]=a;continue;}
  uint64_t key=(uint64_t(g.op)<<48)|(uint64_t(a)<<24)|uint64_t(b);auto found=cache.find(key);
  if(found!=cache.end()){ren[N+k]=found->second;continue;}
  ren[N+k]=N+made.size();cache[key]=ren[N+k];made.push_back({g.op,a,b});
 }
 array<bool,N+G> used{};used[ren[N+G-1]]=true;
 for(int k=(int)made.size()-1;k>=0;k--)if(used[N+k])used[made[k].a]=used[made[k].b]=true;
 int count=0;for(int k=0;k<(int)made.size();k++)count+=used[N+k];
 extra=0;for(auto& group:prefix_groups){int use=0;for(int i:group)use+=used[i];extra+=max(0,use-1);}
 return count+extra<=G;
}
bool accept_shape(const Circuit& c){
 if(!joint_budget_ok(c))return false;
 if(REQUIRE_RAW){array<bool,N+G> used{};used[N+G-1]=true;
  for(int k=G-1;k>=0;k--)if(used[N+k])used[c[k].a]=used[c[k].b]=true;
  for(int i=0;i<RAW_INPUTS;i++)if(!used[i])return false;}
 if(REQUIRE_NONLINEAR)return large_nonlinear(c);
 array<bool,N+G> used{};used[N+G-1]=true;
 for(int k=G-1;k>=0;k--)if(used[N+k])used[c[k].a]=used[c[k].b]=true;
 int count=0;for(int k=0;k<G;k++)count+=used[N+k]&&c[k].op==0&&c[k].a!=c[k].b;
 return count>=MIN_AND;
}
array<Bits,2> gate_context(const Circuit& c,int gate,const array<Bits,N+G>& initial){
 array<Bits,2> result;
 for(int bit=0;bit<2;bit++){
  auto v=initial;v[N+gate].fill(bit?~uint64_t(0):0);
  for(int k=gate+1;k<G;k++){auto g=c[k];for(int w=0;w<W;w++)v[N+k][w]=g.op?(v[g.a][w]|v[g.b][w]):(v[g.a][w]&v[g.b][w]);}
  result[bit]=v[N+G-1];
 }
 return result;
}
Bits replacement_output(const array<Bits,N+G>& v,const array<Bits,2>& context,Gate g){
 Bits output;for(int w=0;w<W;w++){uint64_t value=g.op?(v[g.a][w]|v[g.b][w]):(v[g.a][w]&v[g.b][w]);output[w]=context[0][w]|(context[1][w]&value);}return output;
}
pair<int,int> features(const Circuit& c){
 array<bool,N+G> used{};used[N+G-1]=true;
 for(int k=G-1;k>=0;k--)if(used[N+k])used[c[k].a]=used[c[k].b]=true;
 array<uint64_t,N+G> support;for(int i=0;i<N;i++)support[i]=uint64_t(1)<<i;
 int ac=0,mixed=0;
 for(int k=0;k<G;k++){auto g=c[k];support[N+k]=support[g.a]|support[g.b];if(used[N+k]&&g.op==0&&g.a!=g.b){ac++;
  constexpr uint64_t pmask=(uint64_t(1)<<POINTS)-1;
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
Circuit scatter_free(const Circuit& current){
 vector<Gate> original(current.begin(),current.end());
 while(original.size()>1&&original.back().a==original.back().b&&original.back().a==N+(int)original.size()-2)original.pop_back();
 int count=original.size();if(count==G)return current;
 Circuit result;array<int,N+G> mapping;for(int i=0;i<N;i++)mapping[i]=i;int consumed=0;
 vector<int> positions;for(int i=0;i<G-1;i++)positions.push_back(i);shuffle(positions.begin(),positions.end(),rng);
 positions.resize(count-1);sort(positions.begin(),positions.end());positions.push_back(G-1);
 for(int slot=0;slot<G;slot++){
  int position=positions[consumed];
  if(consumed<count&&slot==position){auto g=original[consumed];result[slot]={g.op,mapping[g.a],mapping[g.b]};mapping[N+consumed]=N+slot;consumed++;}
  else result[slot]={ri(2),ri(N+slot),ri(N+slot)};
 }
 assert(consumed==count&&mapping[N+count-1]==N+G-1);
 assert(values(current)[N+G-1]==values(result)[N+G-1]);return result;
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
 Circuit out;copy(c.begin(),c.end(),out.begin());return scatter_free(REQUIRE_RAW?out:prune(out));
}
void dump(const Circuit& c,const string& path){ofstream f(path);f<<"[\n";for(int k=0;k<G;k++){auto g=c[k];f<<"["<<g.op<<","<<g.a<<","<<g.b<<"]"<<(k+1<G?",":"")<<"\n";}f<<"]\n";}
Circuit topological_shuffle(const Circuit& current){
 array<bool,N+G> active{},line{};array<int,N+G> ren;
 active[N+G-1]=true;for(int k=G-1;k>=0;k--)if(active[N+k])active[current[k].a]=active[current[k].b]=true;
 for(int i=0;i<N;i++){ren[i]=i;line[i]=i>=POINTS;}
 for(int k=0;k<G;k++){ren[N+k]=-1;auto g=current[k];line[N+k]=g.op==1&&line[g.a]&&line[g.b];}
 Circuit result;int count=0;bool prefer_lines=ri(2);
 while(true){
  vector<int> ready,preferred;for(int k=0;k<G;k++)if(active[N+k]&&ren[N+k]<0&&ren[current[k].a]>=0&&ren[current[k].b]>=0){ready.push_back(k);if(line[N+k])preferred.push_back(k);}
  if(ready.empty())break;int k=prefer_lines&&!preferred.empty()?preferred[ri(preferred.size())]:ready[ri(ready.size())];
  auto g=current[k];ren[N+k]=N+count;result[count++]={g.op,ren[g.a],ren[g.b]};
 }
 assert(ren[N+G-1]==N+count-1);int output=ren[N+G-1];
 while(count<G){result[count]={1,output,output};output=N+count++;}
 result=scatter_free(result);assert(values(current)[N+G-1]==values(result)[N+G-1]);return result;
}
Circuit rewrite(const Circuit& current){
 if(ri(8)==0)return topological_shuffle(current);
 array<bool,N+G> active{};active[N+G-1]=true;
 for(int k=G-1;k>=0;k--)if(active[N+k])active[current[k].a]=active[current[k].b]=true;
 vector<int> choices;for(int k=0;k<G;k++)if(active[N+k])choices.push_back(k);
 int chosen=choices[ri(choices.size())],mode=ri(5),unfold=-1;
 pair<int,int> split{-1,-1};
 if(mode==4){vector<int> features;for(int i=RAW_INPUTS;i<N;i++)if(active[i]&&!feature_splits[i].empty())features.push_back(i);
  if(!features.empty()){unfold=features[ri(features.size())];split=feature_splits[unfold][ri(feature_splits[unfold].size())];}}
 if(unfold>=0)unfold_attempts++;
 vector<Gate> made;unordered_map<uint64_t,int> cache;array<int,N+G> memo;memo.fill(-1);
 auto emit=[&](int op,int a,int b){
  if(a==b)return a;if(a>b)swap(a,b);
  uint64_t key=(uint64_t(op)<<48)|(uint64_t(a)<<24)|uint64_t(b);
  auto found=cache.find(key);if(found!=cache.end())return found->second;
  int output=N+made.size();cache[key]=output;made.push_back({op,a,b});return output;
 };
 function<int(int)> build=[&](int wire)->int{
  if(wire<N)return wire==unfold?emit(1,split.first,split.second):wire;if(memo[wire]>=0)return memo[wire];
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
 if(unfold>=0)unfold_success++;
 next=scatter_free(next);assert(values(current)[N+G-1]==values(next)[N+G-1]);
 return next;
}
int main(int argc,char**argv){
 if(argc>=4&&string(argv[1])=="--prefix-groups"){
  ifstream groups(argv[2]);int count;groups>>count;assert(groups&&count>=0);array<bool,N> assigned{};
  while(count--){int width;groups>>width;assert(groups&&width>0);vector<int> group(width);
   for(int&i:group){groups>>i;assert(groups&&i>=RAW_INPUTS&&i<N&&!assigned[i]);assigned[i]=true;}prefix_groups.push_back(group);}
  argc-=2;argv+=2;
 }
 bool polish_mode=false;
 if(argc==7&&string(argv[1])=="--polish"){polish_mode=true;argc--;argv++;}
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
 constexpr uint64_t pmask=(uint64_t(1)<<POINTS)-1,rawmask=(uint64_t(1)<<RAW_INPUTS)-1,lmask=rawmask^pmask;
 uint64_t singleton_inputs=0;bool saw_point_side=false,saw_line_side=false;
 for(int j=0;j<m;j++){uint64_t x;int y;f>>x>>y;for(int i=0;i<N;i++)if(x>>i&1)inputs[i][j/64]|=uint64_t(1)<<(j%64);if(y)target[j/64]|=uint64_t(1)<<(j%64);
  uint64_t raw=x&rawmask;
  if(!y&&popcount(raw&pmask)<=1)owner_priority_mask[j/64]|=uint64_t(1)<<(j%64);
  if(y)for(int p=0;p<POINTS;p++)if(raw>>p&1)owner_positive[p][j/64]|=uint64_t(1)<<(j%64);
  if(popcount(raw)==1&&raw<(uint64_t(1)<<POINTS))point_singleton[countr_zero(raw)]=j;
  assert(x<(uint64_t(1)<<N)&&(y==0||y==1));if(popcount(raw)==1)singleton_inputs|=raw;saw_point_side|=raw==pmask;saw_line_side|=raw==lmask;
  if(popcount(raw)==1||raw==pmask||raw==lmask){assert(y==0);singleton_mask[j/64]|=uint64_t(1)<<(j%64);}
 }
 assert(singleton_inputs==(pmask|lmask)&&saw_point_side&&saw_line_side);
 array<uint64_t,N> raw_support{};
 for(int i=0;i<RAW_INPUTS;i++)raw_support[i]=uint64_t(1)<<i;
 for(int i=RAW_INPUTS;i<N;i++)for(int j=0;j<m;j++){
  uint64_t raw=0;for(int v=0;v<RAW_INPUTS;v++)if(inputs[v][j/64]>>(j%64)&1)raw|=uint64_t(1)<<v;
  if(popcount(raw)==1&&(inputs[i][j/64]>>(j%64)&1))raw_support[i]|=raw;
 }
 for(int i=RAW_INPUTS;i<N;i++){
  Bits expected{};for(int j=0;j<RAW_INPUTS;j++)if(raw_support[i]>>j&1)for(int w=0;w<W;w++)expected[w]|=inputs[j][w];
  assert(expected==inputs[i]);
  for(int a=0;a<N;a++)for(int b=a+1;b<N;b++)if(raw_support[a]&&raw_support[b]&&raw_support[a]!=raw_support[i]&&raw_support[b]!=raw_support[i]&&(raw_support[a]|raw_support[b])==raw_support[i])feature_splits[i].push_back({a,b});
 }
 reload_seeds(argv[2]);
 int duration=stoi(argv[3]);rng.seed(stoull(argv[4]));string prefix=argv[5];
 if(duration==-3){
  int best=100000;long long checked=0;
  for(int index=0;index<(int)seeds.size();index++){
   assert(seeds[index].size()<=G);Circuit initial;int count=0;for(auto g:seeds[index])initial[count++]=g;
   while(count<G){int out=N+count-1;initial[count++]={1,out,out};}
   for(int first=0;first<G;first++)if(initial[first].op==1){
    Circuit base=initial;base[first].op=0;auto v=values(base);
    for(int second=0;second<G;second++)if(second!=first){auto context=gate_context(base,second,v);
     for(int op=0;op<2;op++)for(int a=0;a<N+second;a++)for(int b=a;b<N+second;b++){
      Gate replacement{op,a,b};Bits output=replacement_output(v,context,replacement);checked++;
      auto [miss,wrong]=errors(output);if(miss||singletons(output)||wrong>=best)continue;
      Circuit candidate=base;candidate[second]=replacement;if(!joint_budget_ok(candidate))continue;
      if(wrong!=0&&!accept_shape(candidate))continue;
      assert(values(candidate)[N+G-1]==output);best=wrong;dump(candidate,prefix+"-projected.json");
      cout<<"PROJECT BEST weighted_score "<<best<<" source "<<index<<" first "<<first<<" second "<<second<<" checked "<<checked<<endl;
      if(best==0){dump(candidate,prefix+"-solution.json");cout<<"SOLUTION in finite projection"<<endl;return 0;}
     }
    }
   }
  }
  cout<<"PROJECT DONE checked "<<checked<<" best "<<best<<endl;return 0;
 }
 if(duration==-2){
  ofstream output(prefix+"-budget-fixtures.json");output<<"[\n";
  for(int trial=0;trial<1000;trial++){
   Circuit c;for(int k=0;k<G;k++){
    if(trial%2&&k)c[k]={1,N+k-1,RAW_INPUTS+ri(N-RAW_INPUTS)};
    else c[k]={ri(2),ri(N+k),ri(N+k)};
    if(trial%5==0&&k%3==1)c[k]={ri(2),c[k].a,c[k].a};
    if(trial%7==0&&k)c[k]=c[k-1];
   }
   output<<"{\"accepted\":"<<(joint_budget_ok(c)?"true":"false")<<",\"gates\":[";
   for(int k=0;k<G;k++){auto g=c[k];output<<"["<<g.op<<","<<g.a<<","<<g.b<<"]"<<(k+1<G?",":"");}
   output<<"]}"<<(trial+1<1000?",":"")<<"\n";
  }
  output<<"]\n";cout<<"Wrote 1000 joint-budget fixtures"<<endl;return 0;
 }
 if(duration<0){
  assert(seeds.front().size()<=G);Circuit c;int count=0;for(auto g:seeds.front())c[count++]=g;
  while(count<G){int out=N+count-1;c[count++]={1,out,out};}
  auto before=values(c)[N+G-1];
  for(int trial=0;trial<20000;trial++){
   Circuit base=c;int gate=ri(G);if(trial%2)base[ri(G)]={ri(2),ri(N),ri(N)};
   auto v=values(base);auto context=gate_context(base,gate,v);Gate replacement{ri(2),ri(N+gate),ri(N+gate)};
   auto expected=replacement_output(v,context,replacement);base[gate]=replacement;assert(values(base)[N+G-1]==expected);
  }
  cout<<"PASS 20000 exact gate-context comparisons"<<endl;
  for(int i=0;i<5000;i++)c=rewrite(c);
  assert(values(c)[N+G-1]==before);dump(c,prefix+"-correlated-fixture.json");
  cout<<"PASS 5000 correlated-feature/Boolean rewrites; unfold attempts "<<unfold_attempts<<" accepted "<<unfold_success<<endl;return 0;
 }
 assert(prefix_groups.empty()||polish_mode);
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
 auto savepool=[&](){ofstream f(prefix+"-pool.next.json");f<<"[\n";for(int i=0;i<(int)pool.size();i++){auto [mi,wr]=errors(keys[i]);auto [ac,mx]=features(pool[i]);f<<"{\"miss\":"<<mi<<",\"weighted_score\":"<<wr<<",\"active_and\":"<<ac<<",\"mixed_and\":"<<mx<<",\"gates\":[";for(int k=0;k<G;k++){auto g=pool[i][k];f<<"["<<g.op<<","<<g.a<<","<<g.b<<"]"<<(k+1<G?",":"");}f<<"]}"<<(i+1<(int)pool.size()?",":"")<<"\n";}f<<"]\n";f.close();assert(f);int archive_rename=std::rename((prefix+"-pool.next.json").c_str(),(prefix+"-pool.json").c_str());assert(archive_rename==0);};
 Circuit current=seed(0);Bits sig=values(current)[N+G-1];auto [miss,wrong]=errors(sig);int best=100000,best_all_positive=100000;
 if(miss==0&&singletons(sig)==0){best_all_positive=wrong;dump(current,prefix+"-all-positive.json");cout<<"ALLPOS initial weighted_score "<<wrong<<endl;}
 remember(current,sig);
 if(polish_mode){
  assert(miss==0&&singletons(sig)==0&&accept_shape(current));int global_best=wrong;long long evaluations=0,sweeps=0;
  auto start=chrono::steady_clock::now();int report=-1;Circuit champion=current;
  while(chrono::duration<double>(chrono::steady_clock::now()-start).count()<duration){
   for(int i=0,count=1+ri(12);i<count;i++){auto changed=rewrite(current);if(accept_shape(changed))current=changed;}
   auto initial_values=values(current);Bits initial_sig=initial_values[N+G-1];
   auto initial_errors=errors(initial_sig);assert(initial_errors.first==0&&singletons(initial_sig)==0);
   int optimum=initial_errors.second,ties=0,neutral_ties=0;Circuit winner=current;Bits winning_sig=initial_sig;
   auto resynthesize=[&](const Circuit& base,int gate,const array<Bits,N+G>& v){
    auto context=gate_context(base,gate,v);
    for(int op=0;op<2;op++)for(int a=0;a<N+gate;a++)for(int b=a;b<N+gate;b++){
     Gate replacement{op,a,b};Bits output=replacement_output(v,context,replacement);evaluations++;
     auto [positive_errors,negative_errors]=errors(output);
     if(positive_errors||singletons(output)||negative_errors>optimum)continue;
     Circuit candidate=base;candidate[gate]=replacement;
     if(!joint_budget_ok(candidate))continue;
     if(negative_errors!=0&&!accept_shape(candidate))continue;
     if(negative_errors<optimum){optimum=negative_errors;ties=0;winner=candidate;winning_sig=output;}
     else if(output!=initial_sig&&ri(++ties)==0){winner=candidate;winning_sig=output;}
     else if(output==initial_sig&&winning_sig==initial_sig&&ri(64)==0&&ri(++neutral_ties)==0){winner=candidate;winning_sig=output;}
    }
   };
   if(sweeps%4!=3){for(int gate=0;gate<G;gate++)resynthesize(current,gate,initial_values);}
   else{
    array<bool,N+G> active{};active[N+G-1]=true;
    for(int k=G-1;k>=0;k--)if(active[N+k])active[current[k].a]=active[current[k].b]=true;
    vector<int> choices;for(int k=0;k<G-1;k++)if(active[N+k])choices.push_back(k);
    for(int trial=0;trial<8&&!choices.empty();trial++){
     int first=choices[ri(choices.size())];Circuit base=current;int mode=ri(3);
     if(mode==0)base[first].a=ri(N+first);else if(mode==1)base[first].b=ri(N+first);else base[first].op^=1;
     if(ri(4)==0){int edit=choices[ri(choices.size())],kind=ri(3);
      if(kind==0)base[edit].a=ri(N+edit);else if(kind==1)base[edit].b=ri(N+edit);else base[edit].op^=1;
      first=max(first,edit);}
     auto v=values(base);vector<int> consumers;
     for(int k=first+1;k<G;k++)if(active[N+k]&&(base[k].a==N+first||base[k].b==N+first))consumers.push_back(k);
     for(int repeat=0;repeat<4;repeat++){
      int second=!consumers.empty()&&ri(2)?consumers[ri(consumers.size())]:first+1+ri(G-first-1);
      resynthesize(base,second,v);
     }
    }
   }
   assert(values(winner)[N+G-1]==winning_sig);
   current=winner;sig=winning_sig;wrong=optimum;sweeps++;
   if(sig!=initial_sig||sweeps%1024==0)remember(current,sig);
   if(wrong<global_best){global_best=wrong;champion=current;dump(current,prefix+"-all-positive.json");cout<<"POLISH BEST weighted_score "<<wrong<<" sweep "<<sweeps<<" evaluations "<<evaluations<<endl;}
   if(wrong==0){dump(current,prefix+"-solution.json");cout<<"SOLUTION after exhaustive gate resynthesis"<<endl;return 0;}
   double elapsed=chrono::duration<double>(chrono::steady_clock::now()-start).count();
   if((int)elapsed/10>report){report=(int)elapsed/10;cout<<"POLISH seconds "<<elapsed<<" sweeps "<<sweeps<<" evaluations "<<evaluations<<" best "<<global_best<<" current "<<wrong<<" archive "<<pool.size()<<endl;if(report%3==0)savepool();}
   if(sweeps%100==0){
    if(ri(2))current=champion;
    else if(!pool.empty()&&ri(2))current=pool[ri(pool.size())];
    else{reload_seeds(argv[2]);auto candidate=seed();auto out=values(candidate)[N+G-1];auto e=errors(out);if(e.first==0&&singletons(out)==0&&accept_shape(candidate))current=candidate;}
   }
  }
  savepool();dump(champion,prefix+"-all-positive.json");cout<<"POLISH DONE sweeps "<<sweeps<<" evaluations "<<evaluations<<" best "<<global_best<<endl;return 0;
 }
 long long iterations=0,restarts=0;int report=-1;auto begin=chrono::steady_clock::now();
 while(true){
  double elapsed=chrono::duration<double>(chrono::steady_clock::now()-begin).count();if(elapsed>=duration)break;
  if((int)elapsed/10>report){report=(int)elapsed/10;cout<<"seconds "<<elapsed<<" iterations "<<iterations<<" restarts "<<restarts<<" best "<<best<<" current miss "<<miss<<" weighted_score "<<wrong<<" pool "<<pool.size()<<endl;if(report%3==0)savepool();}
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
  if(nm*3+nw<best&&singletons(nextsig)==0){best=nm*3+nw;dump(next,prefix+"-best.json");cout<<"BEST "<<best<<" miss "<<nm<<" weighted_score "<<nw<<" at "<<elapsed<<endl;}
  if(nm==0&&singletons(nextsig)==0&&nw<best_all_positive){best_all_positive=nw;dump(next,prefix+"-all-positive.json");cout<<"ALLPOS weighted_score "<<nw<<" at "<<elapsed<<endl;}
  if(nm==0&&nw==0){dump(next,prefix+"-solution.json");savepool();cout<<"SOLUTION "<<prefix<<"-solution.json"<<endl;return 0;}
  if(ns<=score||(temp>0&&uniform_real_distribution<double>(0,1)(rng)<exp((score-ns)/temp))){bool changed=nextsig!=sig;current=next;sig=nextsig;miss=nm;wrong=nw;if(iterations%4096==0||(nm==0&&changed))remember(current,sig);}
  iterations++;
  if(iterations%1000000==0){current=prune(current);sig=values(current)[N+G-1];auto e=errors(sig);miss=e.first;wrong=e.second;remember(current,sig);if(miss==0&&singletons(sig)==0&&wrong<best_all_positive){best_all_positive=wrong;dump(current,prefix+"-all-positive.json");cout<<"ALLPOS after pruning weighted_score "<<wrong<<endl;}if(miss==0&&wrong==0){dump(current,prefix+"-solution.json");savepool();cout<<"SOLUTION after pruning"<<endl;return 0;}}
  if(iterations%30000000==0){reload_seeds(argv[2]);current=(!pool.empty()&&ri(2))?pool[ri(pool.size())]:seed();sig=values(current)[N+G-1];auto e=errors(sig);miss=e.first;wrong=e.second;remember(current,sig);restarts++;}
 }
 savepool();cout<<"DONE iterations "<<iterations<<" best "<<best<<" pool "<<pool.size()<<endl;
}
