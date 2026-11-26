#define main original_main
#include "signed-source.cpp"
#undef main
#include "profile-collision.hpp"
#include <cassert>

struct Query { int i,j,op,keeps;uint32_t deleted;Word output;std::vector<int> child;std::pair<int,int> expected; };
double seconds(std::chrono::steady_clock::time_point start){return std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();}
int main(int argc,char**argv){
 std::string source=argv[1];int level=std::stoi(argv[2]),cap=std::stoi(argv[3]),samples=std::stoi(argv[4]);bool allQueries=argc>5&&std::stoi(argv[5]);
 std::ifstream front(source+"/frontier-"+std::to_string(level)+".bin",std::ios::binary),input(source+"/wires.bin",std::ios::binary);
 front.exceptions(std::ios::failbit|std::ios::badbit);input.exceptions(std::ios::failbit|std::ios::badbit);
 uint64_t nw,count;front.read(reinterpret_cast<char*>(&nw),8);front.read(reinterpret_cast<char*>(&count),8);
 std::unordered_map<int,int> mapping;
 auto wire=[&](int id){auto it=mapping.find(id);if(it!=mapping.end())return it->second;Word w;input.seekg(uint64_t(id)*144);input.read(reinterpret_cast<char*>(w.data()),128);int local=intern(w);mapping[id]=local;return local;};
 std::vector<State> states;
 uint64_t stride=std::max(uint64_t(1),count/uint64_t(samples));
 for(uint64_t si=0;si<count;si++){
  uint32_t n,d;front.read(reinterpret_cast<char*>(&n),4);front.read(reinterpret_cast<char*>(&d),4);
  State s;s.ws.resize(n);s.prefix.resize(d);front.read(reinterpret_cast<char*>(s.ws.data()),4*n);front.read(reinterpret_cast<char*>(s.prefix.data()),12*d);
  if(si%stride||states.size()>=size_t(samples))continue;
  for(int&id:s.ws)id=wire(id);for(auto&t:s.prefix){t.a=wire(t.a);t.b=wire(t.b);}states.push_back(std::move(s));
 }
 double specSec=0,oldSec=0,profileSec=0,cachedSec=0,pairedSec=0;uint64_t queries=0,cuts=0,specCount=0,pairCount=0;
 Cov all=covfull();
 for(size_t si=0;si<states.size();si++){
  auto&s=states[si];auto&ws=s.ws;int k=cap-level;
  assert(collision(ws).first<0);
  auto start=std::chrono::steady_clock::now();auto specs=makeSpecs(ws,s.prefix,true,k);specSec+=seconds(start);specCount+=specs.size();
  std::vector<Query> qs;
  for(int i=0;i<int(ws.size());i++)for(int j=i+1;j<int(ws.size());j++)for(int op=0;op<4;op++){
   int a=ws[i],b=ws[j];Word zw=binary(op,wires[a].word,wires[b].word);int zi=intern(zw,op,a,b);Cov cz=wires[zi].cov;
   for(int keeps=0;keeps<4;keeps++){
    uint32_t deleted=(keeps&1?0:1U<<i)|(keeps&2?0:1U<<j);
    if(!allQueries&&ws.size()+1-std::popcount(deleted)>size_t(k))continue;
    Cov cov=cz;for(size_t l=0;l<ws.size();l++)if(!(deleted>>l&1))cov=cor(cov,wires[ws[l]].cov);
    if(!allQueries&&(cov!=all||zw==zero||zw==bneg(zero)||std::find(ws.begin(),ws.end(),zi)!=ws.end()))continue;
    bool cut=false;
    for(auto&sp:specs){if(sp.unavailable&~deleted)continue;auto&p=poolData[sp.pool];int hi=p.bound+sp.constants-std::popcount(sp.constantmask&deleted),lo=k-1+sp.paid;if(lo>hi)continue;Word zr=band(zw,p.domain);bool constant=zr==zero||zr==p.domain;bool av=constant||contains(sp.values,zr);if(lo+!av<hi+constant&&(av||!(sp.unavailable&((1U<<i)|(1U<<j))))){cut=true;break;}}
    if(!allQueries&&cut)continue;
    std::vector<int> child;for(size_t l=0;l<ws.size();l++)if(!(deleted>>l&1))child.push_back(ws[l]);child.push_back(zi);std::sort(child.begin(),child.end());
    qs.push_back({i,j,op,keeps,deleted,zw,std::move(child),{-1,-1}});
   }
  }
  start=std::chrono::steady_clock::now();for(auto&q:qs){q.expected=collision(q.child);cuts+=q.expected.first>=0;}oldSec+=seconds(start);
  ParentProfiles profiles;start=std::chrono::steady_clock::now();assert(profiles.build(ws)==std::pair(-1,-1));profileSec+=seconds(start);
  start=std::chrono::steady_clock::now();for(auto&q:qs){auto actual=profiles.cachedChild(q.deleted,q.output);if(actual!=q.expected){std::cerr<<"cached mismatch "<<si<<" "<<q.i<<" "<<q.j<<" "<<q.op<<" "<<q.keeps<<std::endl;return 2;}}cachedSec+=seconds(start);
  start=std::chrono::steady_clock::now();for(auto&q:qs){auto actual=profiles.pairedChild(q.i,q.j,q.op,q.keeps);if(actual!=q.expected){std::cerr<<"paired mismatch "<<si<<" "<<q.i<<" "<<q.j<<" "<<q.op<<" "<<q.keeps<<" expected "<<q.expected.first<<","<<q.expected.second<<" actual "<<actual.first<<","<<actual.second<<std::endl;return 3;}}pairedSec+=seconds(start);
  for(auto&p:profiles.pairs)pairCount+=p.ready;
  queries+=qs.size();
  if(si%100==99)std::cerr<<"sample="<<si+1<<" queries="<<queries<<std::endl;
 }
 std::cout<<"PASS states="<<states.size()<<" queries="<<queries<<" collisions="<<cuts<<" pair_groups="<<pairCount<<" specs="<<specCount<<" specs_sec="<<specSec<<" old_sec="<<oldSec<<" profile_build_sec="<<profileSec<<" cached_sec="<<cachedSec<<" paired_sec="<<pairedSec<<std::endl;
}
