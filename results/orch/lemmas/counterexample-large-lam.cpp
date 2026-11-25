#include <cstdint>
#include <chrono>
#include <cstdlib>
#include <iostream>
#include <unordered_map>
#include <vector>

struct Gate {int a,b;bool is_or;};
struct Wire {uint64_t f,closure,ancestor;unsigned reach;};
struct Target {unsigned edges;int lower;};
int p,l,n,depth_limit;unsigned point_mask;
std::vector<Gate> gates;
std::vector<Wire> wires;
std::unordered_map<uint64_t,Target> targets;
uint64_t visits[10]{},hits=0,top_hits=0,active_hits=0;
bool failure=false;
int maximum_U=0,maximum_active_U=0;
uint64_t near_hits=0,large_lam_hits=0;
int min_total_slack=100,min_near_slack=100;
std::vector<int> cover_cache;
std::chrono::steady_clock::time_point started;
double time_limit=300;
bool interrupted=false;

int cover_raw(unsigned E) {
  int answer=n;
  for(unsigned s=0;s<(1u<<n);++s) {
    bool good=true;
    for(int a=0;a<p;++a)for(int b=0;b<l;++b)if((E&(1u<<(a*l+b)))&&!(s&(1u<<a))&&!(s&(1u<<(p+b))))good=false;
    if(good&&__builtin_popcount(s)<answer)answer=__builtin_popcount(s);
  }
  return answer;
}

int cover(unsigned E) {return cover_cache[E];}

void residual(uint64_t f,Target target) {
  ++hits;uint64_t clean=0;int c=0,junk=0,other_or=0;
  for(unsigned j=0;j<gates.size();++j)if(!gates[j].is_or&&!(wires[n+j].f&~f))clean|=uint64_t(1)<<j;
  for(unsigned j=0;j<gates.size();++j)if(!gates[j].is_or&&((wires[gates[j].a].ancestor|wires[gates[j].b].ancestor)&clean))return;
  ++top_hits;
  bool active=wires.back().ancestor==((uint64_t(1)<<gates.size())-1);active_hits+=active;
  unsigned U=target.edges;
  for(unsigned j=0;j<gates.size();++j)if(clean&(uint64_t(1)<<j)) {
    auto g=gates[j];unsigned A=wires[g.a].reach,B=wires[g.b].reach;
    c+=!A||!B;
    for(int a=0;a<p;++a)for(int b=0;b<l;++b)if(((A&(1u<<a))&&(B&(1u<<(p+b))))||((B&(1u<<a))&&(A&(1u<<(p+b)))))U&=~(1u<<(a*l+b));
  }
  for(unsigned j=0;j<gates.size();++j) {
    auto g=gates[j];bool dirty=wires[n+j].f&~f;
    if(!g.is_or){junk+=dirty;continue;}
    if(!dirty)continue;
    bool lambda=false;
    if(wires[g.a].reach&&wires[g.b].reach)for(unsigned k=0;k<gates.size();++k)if(clean&(uint64_t(1)<<k)) {
      auto top=gates[k];
      if((__builtin_popcount(wires[top.b].reach)==1&&(wires[top.a].closure&(uint64_t(1)<<j)))||
         (__builtin_popcount(wires[top.a].reach)==1&&(wires[top.b].closure&(uint64_t(1)<<j))))lambda=true;
    }
    lambda = lambda && __builtin_popcount(wires[n+j].reach)>=2;
    large_lam_hits+=lambda;
    other_or+=!lambda;
  }
  int count=__builtin_popcount(U),tau=cover(U);
  int slack=2*c+junk+other_or-count-tau;
  if(active) {
    if(slack<min_total_slack) min_total_slack=slack;
    if(int(gates.size())<=target.lower+2) {
      ++near_hits;
      if(slack<min_near_slack)min_near_slack=slack;
    }
  }
  if(count>maximum_U)maximum_U=count;
  if(active&&count>maximum_active_U)maximum_active_U=count;
  bool total=count+tau<=2*c+junk+other_or,or_bound=count<=c+other_or,and_bound=tau<=c+junk;
  if(!total||!or_bound||!and_bound) {
    std::cout<<"RESIDUAL FAILURE p="<<p<<" l="<<l<<" E="<<target.edges<<" size="<<gates.size()<<" lower="<<target.lower<<" all_active="<<active<<'\n';
    std::cout<<"U="<<U<<" U_card="<<count<<" tau_U="<<tau<<" c="<<c<<" j="<<junk<<" o="<<other_or<<" total="<<total<<" OR="<<or_bound<<" AND="<<and_bound<<'\n';
    for(auto z:gates)std::cout<<(z.is_or?"OR ":"AND ")<<z.a<<' '<<z.b<<'\n';
    failure=true;std::cout.flush();
  }
}

void search(int d) {
  ++visits[d];
  if((visits[d]&((1u<<20)-1))==0 && std::chrono::duration<double>(std::chrono::steady_clock::now()-started).count()>time_limit) {
    interrupted=true;return;
  }
  if(d==depth_limit)return;
  int count=wires.size();
  for(int a=0;a<count;++a)for(int b=a;b<count;++b)for(int op=0;op<2;++op) {
    unsigned reach=op?(wires[a].reach|wires[b].reach):0;
    if((reach&point_mask)&&(reach&~point_mask))continue;
    Wire w;
    w.f=op?(wires[a].f|wires[b].f):(wires[a].f&wires[b].f);w.reach=reach;
    w.closure=(uint64_t(1)<<d)|(op?(wires[a].closure|wires[b].closure):0);
    w.ancestor=(uint64_t(1)<<d)|wires[a].ancestor|wires[b].ancestor;
    wires.push_back(w);gates.push_back({a,b,bool(op)});
    auto target=targets.find(w.f);if(target!=targets.end())residual(w.f,target->second);
    if(failure||interrupted)return;
    search(d+1);if(failure||interrupted)return;
    gates.pop_back();wires.pop_back();
  }
}

int main(int argc,char**argv) {
  p=argc>1?std::atoi(argv[1]):2;l=argc>2?std::atoi(argv[2]):2;depth_limit=argc>3?std::atoi(argv[3]):5;n=p+l;
  if(n>6||depth_limit>8)return 2;point_mask=(1u<<p)-1;
  if(argc>4)time_limit=std::atof(argv[4]);
  cover_cache.resize(1u<<(p*l));for(unsigned E=0;E<cover_cache.size();++E)cover_cache[E]=cover_raw(E);
  started=std::chrono::steady_clock::now();
  std::cout<<"largeLam raw enumeration p="<<p<<" l="<<l<<" depth="<<depth_limit<<" seconds_limit="<<time_limit<<std::endl;
  for(unsigned E=1;E<(1u<<(p*l));++E){
    auto edge=[&](int a,int b){return bool(E&(1u<<(a*l+b)));};bool four=false;
    for(int a=0;a<p;++a)for(int aa=a+1;aa<p;++aa)for(int b=0;b<l;++b)for(int bb=b+1;bb<l;++bb)if(edge(a,b)&&edge(a,bb)&&edge(aa,b)&&edge(aa,bb))four=true;
    if(four)continue;uint64_t f=0;
    for(unsigned x=0;x<(1u<<n);++x)for(int a=0;a<p;++a)for(int b=0;b<l;++b)if(edge(a,b)&&(x&(1u<<a))&&(x&(1u<<(p+b))))f|=uint64_t(1)<<x;
    targets.emplace(f,Target{E,__builtin_popcount(E)+cover(E)-1});
  }
  for(int i=0;i<n;++i){uint64_t f=0;for(unsigned x=0;x<(1u<<n);++x)if(x&(1u<<i))f|=uint64_t(1)<<x;wires.push_back({f,0,0,1u<<i});}
  search(0);
  for(int d=0;d<=depth_limit;++d)std::cout<<"depth "<<d<<" raw_states "<<visits[d]<<'\n';
  std::cout<<"graph_outputs="<<hits<<" top_form="<<top_hits<<" top_form_all_active="<<active_hits<<'\n';
  std::cout<<"maximum_U="<<maximum_U<<" maximum_all_active_U="<<maximum_active_U<<'\n';
  std::cout<<"largeLam incidences="<<large_lam_hits<<" near_minimum_all_active="<<near_hits<<" minimum_active_total_slack="<<min_total_slack<<" minimum_near_total_slack="<<min_near_slack<<'\n';
  std::cout<<"elapsed_seconds="<<std::chrono::duration<double>(std::chrono::steady_clock::now()-started).count()<<'\n';
  std::cout<<(failure?"FAILURE":(interrupted?"INCOMPLETE TIME LIMIT; NO FAILURE IN VISITED PREFIX":"EXHAUSTIVE COMPLETE; ALL THREE LARGE-LAM RESIDUAL INEQUALITIES PASS"))<<std::endl;
  return failure?1:(interrupted?3:0);
}
