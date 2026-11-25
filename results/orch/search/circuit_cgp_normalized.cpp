#include <algorithm>
#include <array>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <numeric>
#include <random>
#include <vector>
struct Gate {int op,a,b;};
struct Instance {int n,k,m,upperk;uint64_t target;std::vector<uint64_t> inputs;std::vector<Gate> upper;};
struct Normal {std::array<Gate,60> gates{};int size=0,output=0,ors=0;};
Instance load(const char *path){std::ifstream in(path);Instance z;in>>z.n>>z.k>>z.m>>z.target>>z.upperk;z.inputs.resize(z.n);for(auto &v:z.inputs)in>>v;z.upper.resize(z.upperk);for(auto &g:z.upper)in>>g.op>>g.a>>g.b;if(!in||z.m>64||z.n!=14)throw 1;return z;}
int main(int argc,char **argv){
 if(argc!=7){std::cerr<<"usage: normalized_cgp honest.input dirty.input seconds seed capacity controls\n";return 2;}
 Instance a=load(argv[1]),b=load(argv[2]);if(a.n!=b.n||a.m!=b.m||a.target!=b.target||a.inputs!=b.inputs)return 3;
 int n=a.n,cap=std::stoi(argv[5]),seconds=std::stoi(argv[3]);bool controls=std::stoi(argv[6]);if(cap<29||cap>60)return 4;
 uint64_t all=a.m==64?~0ULL:(1ULL<<a.m)-1;std::mt19937_64 rng(std::stoull(argv[4]));
 auto start=std::chrono::steady_clock::now();auto elapsed=[&](){return std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();};
 std::vector<unsigned> edge_masks;for(int bit=0;bit<a.m;bit++)if(a.target>>bit&1){unsigned mask=0;for(int i=0;i<n;i++)if(a.inputs[i]>>bit&1)mask|=1U<<i;if(__builtin_popcount(mask)!=2) return 5;edge_masks.push_back(mask);}
 auto evaluate=[&](const std::vector<Gate>& c,std::array<uint64_t,128>& values){for(int i=0;i<n;i++)values[i]=a.inputs[i];for(int j=0;j<cap;j++)values[n+j]=c[j].op?(values[c[j].a]|values[c[j].b]):(values[c[j].a]&values[c[j].b]);};
 auto normalize=[&](const std::vector<Gate>& c,int output,const std::array<uint64_t,128>& values){
  Normal built;std::array<int,128> map{},slots{};slots.fill(-3);std::array<uint64_t,128> keys{};
  auto bucket=[](uint64_t x){x^=x>>33;x*=0xff51afd7ed558ccdULL;x^=x>>33;return unsigned(x)&127;};
  auto insert=[&](uint64_t key,int wire){unsigned at=bucket(key);while(slots[at]!=-3&&keys[at]!=key)at=(at+1)&127;keys[at]=key;slots[at]=wire;};
  for(int i=0;i<n;i++){map[i]=i;insert(values[i],i);}
  for(int j=0;j<cap;j++){
   uint64_t value=values[n+j];if(value==0){map[n+j]=-1;continue;}if(value==all){map[n+j]=-2;continue;}
   unsigned at=bucket(value);while(slots[at]!=-3&&keys[at]!=value)at=(at+1)&127;
   if(slots[at]!=-3){map[n+j]=slots[at];continue;}
   int u=map[c[j].a],v=map[c[j].b];if(u<0||v<0)throw 6;if(u>v)std::swap(u,v);
   int wire=n+built.size;built.gates[built.size++]={c[j].op,u,v};map[n+j]=wire;keys[at]=value;slots[at]=wire;
  }
  int out=map[output];if(out<0)throw 7;
  uint64_t active=out<n?0:1ULL<<(out-n);for(int j=built.size-1;j>=0;j--)if(active>>j&1){auto g=built.gates[j];if(g.a>=n)active|=1ULL<<(g.a-n);if(g.b>=n)active|=1ULL<<(g.b-n);}
  Normal result;std::array<int,128> ren{};for(int i=0;i<n;i++)ren[i]=i;
  for(int j=0;j<built.size;j++)if(active>>j&1){auto g=built.gates[j];ren[n+j]=n+result.size;result.gates[result.size++]={g.op,ren[g.a],ren[g.b]};result.ors+=g.op;}
  result.output=ren[out];return result;
 };
 auto fresh=[&](const Instance& z){
  std::vector<Gate> c(cap),topo;std::vector<int> done(z.upperk),ren(n+z.upperk,-1);for(int i=0;i<n;i++)ren[i]=i;
  for(int j=0;j<z.upperk;j++){std::vector<int> ready;for(int h=0;h<z.upperk;h++)if(!done[h]&&ren[z.upper[h].a]>=0&&ren[z.upper[h].b]>=0)ready.push_back(h);int h=ready[rng()%ready.size()];topo.push_back({z.upper[h].op,ren[z.upper[h].a],ren[z.upper[h].b]});done[h]=1;ren[n+h]=n+j;}
  std::vector<int> positions(cap-1);std::iota(positions.begin(),positions.end(),0);std::shuffle(positions.begin(),positions.end(),rng);positions.resize(z.upperk-1);positions.push_back(cap-1);std::sort(positions.begin(),positions.end());
  std::vector<int> map(n+z.upperk);for(int i=0;i<n;i++)map[i]=i;for(int j=0;j<z.upperk;j++)map[n+j]=n+positions[j];
  for(int j=0;j<cap;j++)c[j]={int(rng()&1),int(rng()%(n+j)),int(rng()%(n+j))};for(int j=0;j<z.upperk;j++)c[positions[j]]={topo[j].op,map[topo[j].a],map[topo[j].b]};return c;
 };
 auto unread=[&](const Normal& r){std::array<uint64_t,128>p{},l{},pairs{};for(int i=0;i<n;i++)(i<7?p[i]:l[i])=a.inputs[i]&a.target;for(int j=0;j<r.size;j++){auto g=r.gates[j];if(g.op){p[n+j]=p[g.a]|p[g.b];l[n+j]=l[g.a]|l[g.b];pairs[n+j]=pairs[g.a]|pairs[g.b];}else pairs[n+j]=(p[g.a]&l[g.b])|(l[g.a]&p[g.b]);}return a.target&~pairs[r.output];};
 auto full_verify=[&](const Normal& r){
  if(r.output<0||r.output>=n+r.size)return false;for(int j=0;j<r.size;j++){auto g=r.gates[j];if(g.op<0||g.op>1||g.a<0||g.b<0||g.a>=n+j||g.b>=n+j)return false;}
  for(unsigned mask=0;mask<(1U<<n);mask++){std::array<bool,128>w{};for(int i=0;i<n;i++)w[i]=mask>>i&1;for(int j=0;j<r.size;j++){auto g=r.gates[j];w[n+j]=g.op?(w[g.a]||w[g.b]):(w[g.a]&&w[g.b]);}bool expected=false;for(unsigned e:edge_masks)if((mask&e)==e){expected=true;break;}if(w[r.output]!=expected)return false;}return true;
 };
 auto print=[&](const Normal& r,const char *kind,uint64_t iterations,uint64_t restarts){
  if(!full_verify(r))throw 8;
  std::cout<<"{\"kind\":\""<<kind<<"\",\"seconds\":"<<elapsed()<<",\"active_gates\":"<<r.size<<",\"or_gates\":"<<r.ors<<",\"and_gates\":"<<r.size-r.ors<<",\"total_gates\":"<<cap<<",\"semantic_normalization\":true,\"virtual_constants_eliminated\":true,\"full_inputs_verified\":"<<(1U<<n)<<",\"iterations\":"<<iterations<<",\"restarts\":"<<restarts<<",\"score\":0,\"unread_mask\":"<<unread(r)<<",\"gates\":[";
  for(int j=0;j<r.size;j++){auto g=r.gates[j];if(j)std::cout<<',';std::cout<<'['<<g.op<<','<<g.a<<','<<g.b<<']';}std::cout<<"],\"output\":"<<r.output<<'}'<<std::endl;
 };
 std::array<uint64_t,128>values{};
 for(const auto *z:{&a,&b}){auto c=fresh(*z);evaluate(c,values);if(values[n+cap-1]!=a.target)return 9;auto r=normalize(c,n+cap-1,values);if(r.size>z->upperk)return 10;if(r.size<=26){print(r,"counterexample_candidate",0,0);return 11;}print(r,z==&a?"control_honest":"control_dirty",0,0);}
 if(controls)return 0;
 int best=1000,best_or=20;bool found_unread27=false;uint64_t total=0,restarts=0;Normal best_normal;
 while(elapsed()<seconds){
  restarts++;auto c=fresh((rng()&1)?a:b);int output=n+cap-1;evaluate(c,values);Normal current=normalize(c,output,values);if(current.size<=26){print(current,"counterexample_candidate",total,restarts);return 11;}int energy=current.size+3*current.ors;
  for(int iter=0;iter<2000000;iter++){
   if((iter&8191)==0&&elapsed()>=seconds){print(best_normal,"final",total,restarts);return 0;}
   total++;bool output_change=rng()%64==0;int oldout=output,j=rng()%cap;Gate old=c[j],g=old;
   if(output_change)output=rng()%(n+cap);else{switch(rng()%8){case 0:g.op^=1;break;case 1:case 2:case 3:g.a=rng()%(n+j);break;case 4:case 5:case 6:g.b=rng()%(n+j);break;default:g.op=rng()%2;g.a=rng()%(n+j);g.b=rng()%(n+j);break;}c[j]=g;}
   evaluate(c,values);if(values[output]!=a.target){c[j]=old;output=oldout;continue;}
   Normal candidate=normalize(c,output,values);
   if(candidate.size<=26){print(candidate,"counterexample_candidate",total,restarts);return 11;}
   if(candidate.ors<best_or){best_or=candidate.ors;print(candidate,"or_bound_candidate",total,restarts);}
   if(candidate.size==27&&!found_unread27&&unread(candidate)){found_unread27=true;print(candidate,"unread_27",total,restarts);}
   int ne=candidate.size+3*candidate.ors;double temperature=.1+2.*(1.-double(iter)/2000000.);
   if(ne<=energy||double(rng())/double(UINT64_MAX)<std::exp(double(energy-ne)/temperature)){current=candidate;energy=ne;}else{c[j]=old;output=oldout;}
   if(current.size<best){best=current.size;best_normal=current;print(current,"improvement",total,restarts);}
  }
 }
 print(best_normal,"final",total,restarts);return 0;
}
