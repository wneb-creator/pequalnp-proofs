#include "probe-data.hpp"
constexpr bool signedMode=true;

#include <algorithm>
#include <bit>
#include <chrono>
#include <iostream>
#include <iomanip>
#include <map>
#include <unordered_map>
#include <unordered_set>
#include <filesystem>

struct WHash { size_t operator()(const Word&w) const {size_t h=0;for(auto x:w)h^=(x+0x9e3779b97f4a7c15ULL+(h<<6)+(h>>2));return h;} };
Word band(const Word&a,const Word&b){Word w;for(int i=0;i<16;i++)w[i]=a[i]&b[i];return w;}
Word bor(const Word&a,const Word&b){Word w;for(int i=0;i<16;i++)w[i]=a[i]|b[i];return w;}
Word bneg(const Word&a){Word w;for(int i=0;i<16;i++)w[i]=~a[i];return w;}
Word binary(int op,const Word&a,const Word&b){return op==0?band(a,b):op==1?bor(a,b):op==2?band(a,bneg(b)):band(bneg(a),b);}
bool bit(const Word&w,int n){return (w[n/64]>>(n%64))&1;}
Word zero{};
using Cov=std::array<uint64_t,4>;
Cov coverage(const Word&w){Cov c{};for(size_t i=0;i<boundaryPairs.size();i++){auto[p,n]=boundaryPairs[i];if(signedMode?(bit(w,p)!=bit(w,n)):(bit(w,p)&&!bit(w,n)))c[i/64]|=1ULL<<(i%64);}return c;}
Cov covfull(){Cov c{};for(size_t i=0;i<boundaryPairs.size();i++)c[i/64]|=1ULL<<(i%64);return c;}
Cov cor(Cov a,const Cov&b){for(int i=0;i<4;i++)a[i]|=b[i];return a;}
struct Wire{Word word;Cov cov;int op,a,b,var;};
std::vector<Wire>wires;
// Hash keys narrow candidate buckets only. Full truth tables always decide identity.
std::unordered_multimap<size_t,int> wireHashIds;
size_t wireHash(const Word&w){
#ifdef FORCE_WIRE_HASH_COLLISIONS
 (void)w;return 0;
#else
 return WHash{}(w);
#endif
}
int lookupWire(const Word&w,size_t h){auto[first,last]=wireHashIds.equal_range(h);for(auto it=first;it!=last;++it)if(wires[it->second].word==w)return it->second;return -1;}
int lookupWire(const Word&w){return lookupWire(w,wireHash(w));}
int intern(const Word&w,int op=-1,int a=-1,int b=-1,int var=-1){size_t h=wireHash(w);int old=lookupWire(w,h);if(old>=0)return old;int id=wires.size();wires.push_back({w,coverage(w),op,a,b,var});wireHashIds.emplace(h,id);return id;}
std::vector<std::array<int,1024>> rowPerms;
std::unordered_map<uint64_t,int> imageIds;
int imageWire(int id,int p){
 if(p==0)return id;
 uint64_t key=(uint64_t(id)<<7)|p;auto it=imageIds.find(key);if(it!=imageIds.end())return it->second;
 Wire orig=wires[id];int mapped;
 if(orig.var>=0)mapped=automorphisms[p][orig.var];
 else if(orig.op>=0){int a=imageWire(orig.a,p),b=imageWire(orig.b,p);Word w=binary(orig.op,wires[a].word,wires[b].word);mapped=intern(w,orig.op,a,b);}
 else {Word w{};for(int r=0;r<1024;r++)if(bit(orig.word,rowPerms[p][r]))w[r/64]|=1ULL<<(r%64);mapped=intern(w);}
 imageIds.emplace(key,mapped);return mapped;
}
std::vector<int> canonical(const std::vector<int>&ws){
 std::vector<int> best=ws;std::sort(best.begin(),best.end());
 for(size_t p=1;p<rowPerms.size();p++){
  std::vector<int> candidate;for(int w:ws)candidate.push_back(imageWire(w,p));std::sort(candidate.begin(),candidate.end());
  if(candidate<best)best=std::move(candidate);
 }
 return best;
}
struct Step{int op,a,b;};
struct Spec{int pool,paid,constants;uint32_t unavailable,constantmask;std::vector<Word> values;};
bool contains(const std::vector<Word>&ws,const Word&w){return std::find(ws.begin(),ws.end(),w)!=ws.end();}
std::vector<Spec> makeSpecs(const std::vector<int>&ws,const std::vector<Step>&prefix,bool allPaid,int cap){
 std::vector<Spec> answer;
 static std::vector<std::vector<int>> sampleRows=[](){
  std::vector<std::vector<int>> out;
  for(auto&p:poolData){std::vector<int> rows;for(int r=0;r<1024;r++)if(bit(p.domain,r))rows.push_back(r);if(rows.empty())throw std::runtime_error("empty pool domain");
   std::vector<int> samples={rows.front(),rows.back()};
   for(int j=1;j<=4;j++)samples.push_back(rows[(rows.size()-1)*j/5]);out.push_back(std::move(samples));
  }return out;
 }();
 for(size_t pi=0;pi<poolData.size();pi++){
  auto&p=poolData[pi];
  int constantsUpper=ws.size();
  for(int id:ws){bool first=bit(wires[id].word,sampleRows[pi][0]);for(size_t j=1;j<sampleRows[pi].size();j++)if(bit(wires[id].word,sampleRows[pi][j])!=first){constantsUpper--;break;}}
  if(p.bound+constantsUpper<cap-1)continue;
  uint32_t cm=0;
  std::vector<Word> masked;
  for(size_t i=0;i<ws.size();i++){Word w=band(wires[ws[i]].word,p.domain);masked.push_back(w);if(w==zero||w==p.domain)cm|=1U<<i;}
  int maxPaid=p.bound+std::popcount(cm)-(cap-1);
  if(maxPaid<0)continue;
  std::vector<std::pair<std::vector<Word>,int>> banks{{{},0}};
  for(size_t si=0;si<prefix.size()&&(allPaid||si==0);si++){
   auto s=prefix[si];Word a=band(wires[s.a].word,p.domain),b=band(wires[s.b].word,p.domain),z=binary(s.op,a,b);
   size_t sz=banks.size();
   for(size_t i=0;i<sz;i++)if(banks[i].second<maxPaid&&(contains(p.wires,a)||contains(banks[i].first,a))&&(contains(p.wires,b)||contains(banks[i].first,b))&&!contains(p.wires,z)&&!contains(banks[i].first,z)){
    auto bank=banks[i];bank.first.push_back(z);if(signedMode)bank.first.push_back(band(bneg(z),p.domain));bank.second++;banks.push_back(std::move(bank));
   }
  }
  for(auto&[vals,paid]:banks){
   uint32_t un=0;
   for(size_t i=0;i<ws.size();i++){
    Word v=masked[i];
    if(!contains(p.wires,v)&&!contains(vals,v))un|=1U<<i;
   }
   if(std::popcount(un)<=2)answer.push_back({int(pi),paid,std::popcount(cm),un,cm,std::move(vals)});
  }
 }
 return answer;
}
struct VecHash{size_t operator()(const std::vector<int>&w)const{size_t h=0;for(int x:w)h^=size_t(x)+0x9e3779b97f4a7c15ULL+(h<<6)+(h>>2);return h;}};
struct State{std::vector<int> ws;std::vector<Step> prefix;};
std::pair<int,int> collision(const std::vector<int>&ws){
 if(ws.size()>20)throw std::runtime_error("collision width exceeds static table");
 static std::vector<int> representative(1U<<20);
 static std::vector<uint32_t> stamps(1U<<20,0);
 static uint32_t stamp=0;
 if(++stamp==0){std::fill(stamps.begin(),stamps.end(),0);stamp=1;}
 for(int r=0;r<1024;r++){
  unsigned profile=0;for(size_t i=0;i<ws.size();i++)if(bit(wires[ws[i]].word,r))profile|=1U<<i;
  int s=representative[profile];
  if(stamps[profile]==stamp&&bit(target,r)!=bit(target,s))return bit(target,r)?std::pair(r,s):std::pair(s,r);
  representative[profile]=r;stamps[profile]=stamp;
 }
 return {-1,-1};
}
#include "cached-collision.hpp"
void writeTarget(const std::vector<Step>&prefix,int op,int a,int b){
 std::ofstream out("target.json");std::map<int,int> slots;for(int i=0;i<10;i++)slots[i]=i;
 out<<"{\"inputs\":10,\"gate_count\":"<<prefix.size()+1<<",\"gates\":[";
 bool first=true;int step=0;
 auto emit=[&](const Step&t){if(!first)out<<",";first=false;if(!slots.contains(t.a)||!slots.contains(t.b))throw std::runtime_error("target operand not supplied");out<<"["<<t.op<<","<<slots[t.a]<<","<<slots[t.b]<<"]";int id=lookupWire(binary(t.op,wires[t.a].word,wires[t.b].word));if(id<0)throw std::runtime_error("target word missing");slots[id]=10+step;step++;};
 for(auto&t:prefix)emit(t);
 if(!first)out<<",";out<<"["<<op<<","<<slots.at(a)<<","<<slots.at(b)<<"]],\"output\":"<<10+prefix.size()<<"}\n";out.close();if(!out)throw std::runtime_error("target write/close failure");
}
int main(int argc,char**argv){
 int depth=argc>1?std::stoi(argv[1]):3;bool allPaid=argc<3||std::stoi(argv[2]);
 int capLimit=argc>3?std::stoi(argv[3]):16;
 std::filesystem::path resumeSource;
 if(argc>4){if(argc!=6)throw std::runtime_error("resume requires source directory and level");resumeSource=std::filesystem::canonical(argv[4]);if(resumeSource==std::filesystem::canonical(std::filesystem::current_path()))throw std::runtime_error("resume source and output directory must differ");}
 bool fullSeparation=true;
 std::map<std::pair<int,int>,int> pairCounts;
 std::ofstream factorStates("factor-states.bin",std::ios::binary);
 std::ofstream wireTrace("wires.bin",std::ios::binary);if(!wireTrace||!factorStates)throw std::runtime_error("cannot open trace output");factorStates.close();if(!factorStates)throw std::runtime_error("factor trace close failure");
 size_t writtenWires=0;
 auto dumpWires=[&](){for(;writtenWires<wires.size();writtenWires++){auto&w=wires[writtenWires];wireTrace.write(reinterpret_cast<const char*>(w.word.data()),128);int origin[4]={w.op,w.a,w.b,w.var};wireTrace.write(reinterpret_cast<const char*>(origin),16);}wireTrace.flush();if(!wireTrace)throw std::runtime_error("wire trace write failure");};
 auto checkpoint=[&](int level,const std::vector<State>&states){dumpWires();std::ofstream out("frontier-"+std::to_string(level)+".bin",std::ios::binary);uint64_t count=states.size(),nw=wires.size();out.write(reinterpret_cast<char*>(&nw),8);out.write(reinterpret_cast<char*>(&count),8);for(auto&s:states){uint32_t n=s.ws.size(),d=s.prefix.size();out.write(reinterpret_cast<char*>(&n),4);out.write(reinterpret_cast<char*>(&d),4);out.write(reinterpret_cast<const char*>(s.ws.data()),4*n);out.write(reinterpret_cast<const char*>(s.prefix.data()),12*d);}out.close();if(!out)throw std::runtime_error("frontier write/close failure");};
 auto begin=std::chrono::steady_clock::now();
 std::vector<int> base;for(size_t i=0;i<rawInputs.size();i++)base.push_back(intern(rawInputs[i],-1,-1,-1,int(i)));
 for(auto&p:automorphisms){std::array<int,1024> rp;for(int r=0;r<1024;r++){int s=0;for(int i=0;i<10;i++)if(r>>p[i]&1)s|=1<<i;rp[r]=s;}rowPerms.push_back(rp);}
 std::unordered_map<std::vector<int>,int,VecHash> known;
 for(auto&[k,state]:knownStates){std::vector<int> ws;for(auto&w:state)ws.push_back(intern(w));auto key=canonical(ws);auto[it,ok]=known.emplace(key,k);if(!ok&&it->second<k)it->second=k;}
 std::sort(base.begin(),base.end());
 std::vector<State> work{{base,{}}};Cov all=covfull();
 int startLevel=0;
 if(argc>5){
  std::filesystem::path source=resumeSource;startLevel=std::stoi(argv[5]);
  if(startLevel<0||startLevel>depth||startLevel>capLimit)throw std::runtime_error("bad resume level");
  std::ifstream front(source/("frontier-"+std::to_string(startLevel)+".bin"),std::ios::binary);
  uint64_t nw=0,ns=0;front.read(reinterpret_cast<char*>(&nw),8);front.read(reinterpret_cast<char*>(&ns),8);
  if(!front||nw<10)throw std::runtime_error("bad resume frontier header");
  std::ifstream inputWires(source/"wires.bin",std::ios::binary);
  for(uint64_t i=0;i<nw;i++){
   Word w{};int origin[4]={-1,-1,-1,-1};inputWires.read(reinterpret_cast<char*>(w.data()),128);inputWires.read(reinterpret_cast<char*>(origin),16);
   if(!inputWires)throw std::runtime_error("truncated resume wire record");
   if(i<10){if(w!=rawInputs[i]||origin[0]!=-1||origin[1]!=-1||origin[2]!=-1||origin[3]!=int(i))throw std::runtime_error("bad resume raw input");}
   else {if(origin[0]<0||origin[0]>3||origin[1]<0||origin[2]<0||uint64_t(origin[1])>=i||uint64_t(origin[2])>=i||origin[3]!=-1)throw std::runtime_error("bad resume wire expression");if(w!=binary(origin[0],wires[origin[1]].word,wires[origin[2]].word))throw std::runtime_error("bad resume wire equation");}
   if(intern(w,origin[0],origin[1],origin[2],origin[3])!=int(i))throw std::runtime_error("bad resume wire ID or duplicate");
  }
  work.clear();work.reserve(ns);
  for(uint64_t i=0;i<ns;i++){
   uint32_t n=0,d=0;front.read(reinterpret_cast<char*>(&n),4);front.read(reinterpret_cast<char*>(&d),4);
   if(!front)throw std::runtime_error("truncated resume state header");
   if(n>20||d!=uint32_t(startLevel))throw std::runtime_error("bad resume state width/depth");
   State s;s.ws.resize(n);s.prefix.resize(d);front.read(reinterpret_cast<char*>(s.ws.data()),4*n);front.read(reinterpret_cast<char*>(s.prefix.data()),12*d);
   if(!front)throw std::runtime_error("truncated resume state");
   for(int id:s.ws)if(id<0||uint64_t(id)>=nw)throw std::runtime_error("bad resume live ID");
   for(auto t:s.prefix)if(t.op<0||t.op>3||t.a<0||t.b<0||uint64_t(t.a)>=nw||uint64_t(t.b)>=nw)throw std::runtime_error("bad resume prefix");
   std::unordered_set<int> supplied;for(int j=0;j<10;j++)supplied.insert(j);
   for(auto t:s.prefix){if(!supplied.contains(t.a)||!supplied.contains(t.b)||t.a==t.b)throw std::runtime_error("noncausal resume prefix");int id=lookupWire(binary(t.op,wires[t.a].word,wires[t.b].word));if(id<0)throw std::runtime_error("missing resume prefix result");supplied.insert(id);}
   std::unordered_set<int> live;
   for(int id:s.ws){if(!live.insert(id).second||!supplied.contains(id)||wires[id].word==zero||wires[id].word==bneg(zero))throw std::runtime_error("duplicate, unavailable or constant resume live wire");}
   work.push_back(std::move(s));
  }
  if(front.peek()!=std::ifstream::traits_type::eof())throw std::runtime_error("trailing resume frontier data");
  std::cerr<<"RESUMED level="<<startLevel<<" states="<<work.size()<<" wires="<<wires.size()<<std::endl;
 }
 checkpoint(startLevel,work);
 for(int level=startLevel;level<depth;level++){
  uint64_t moves=0,lenCuts=0,sepCuts=0,redCuts=0,projCuts=0,linkCuts=0,factorCuts=0,fullCuts=0,open=0;
  int k=capLimit-level;
  std::unordered_map<std::vector<int>,size_t,VecHash> seen;
  std::vector<State> next;
  size_t done=0;
  for(auto&state:work){
   const auto&ws=state.ws;
   for(int w:ws)if(wires[w].word==target){std::cerr<<"TARGET PRESENT at level "<<level+1<<" width "<<ws.size()<<std::endl;return 4;}
   CachedProfiles profiles;
   if(fullSeparation){auto pair=profiles.build(ws);if(pair.first>=0){fullCuts++;pairCounts[pair]++;continue;}}
   auto specs=makeSpecs(ws,state.prefix,allPaid,k);
   for(size_t i=0;i<ws.size();i++)for(size_t j=i+1;j<ws.size();j++)for(int op=0;op<(signedMode?4:2);op++){
    int a=ws[i],b=ws[j];Word zw=binary(op,wires[a].word,wires[b].word);if(zw==target){std::cerr<<"TARGET GENERATED at level "<<level+1<<" op "<<op<<" left "<<a<<" right "<<b<<std::endl;writeTarget(state.prefix,op,a,b);checkpoint(level,work);dumpWires();wireTrace.close();if(!wireTrace)throw std::runtime_error("wire trace close failure");return 4;}int zi=intern(zw,op,a,b);Cov cz=wires[zi].cov;
    for(int keeps=0;keeps<4;keeps++){
     moves++;bool ka=keeps&1,kb=keeps&2;uint32_t deleted=(ka?0:1U<<i)|(kb?0:1U<<j);
     if(ws.size()+1-std::popcount(deleted)>size_t(k)){lenCuts++;continue;}
     Cov cov=cz;for(size_t l=0;l<ws.size();l++)if(!(deleted>>l&1))cov=cor(cov,wires[ws[l]].cov);
     if(cov!=all){sepCuts++;continue;}
     if(zw==zero||zw==bneg(zero)||std::find(ws.begin(),ws.end(),zi)!=ws.end()){redCuts++;continue;}
     bool cut=false;
     for(auto&s:specs){
      if(s.unavailable&~deleted)continue;
      auto&p=poolData[s.pool];int hi=p.bound+s.constants-std::popcount(s.constantmask&deleted),lo=k-1+s.paid;
      if(lo>hi)continue;
      Word zr=band(zw,p.domain);bool constant=zr==zero||zr==p.domain;
      bool av=constant||contains(p.wires,zr)||contains(s.values,zr);
      if(lo+!av<hi+constant&&(av||!(s.unavailable&((1U<<i)|(1U<<j))))){cut=true;break;}
     }
     if(cut){projCuts++;continue;}
     std::vector<int> child;for(size_t l=0;l<ws.size();l++)if(!(deleted>>l&1))child.push_back(ws[l]);child.push_back(zi);std::sort(child.begin(),child.end());
     auto missing=profiles.child(deleted,zw);if(missing.first>=0){fullCuts++;pairCounts[missing]++;continue;}
     auto key=canonical(child);auto ik=known.find(key);if(ik!=known.end()&&ik->second>=k-1){linkCuts++;continue;}
     open++;auto[it,ok]=seen.emplace(std::move(key),next.size());
     if(ok){auto prefix=state.prefix;prefix.push_back({op,a,b});next.push_back({std::move(child),std::move(prefix)});}
    }
   }
   if(++done%10000==0)std::cerr<<"level "<<level+1<<" progress "<<done<<"/"<<work.size()<<" states "<<next.size()<<" wires "<<wires.size()<<std::endl;
  }
  double sec=std::chrono::duration<double>(std::chrono::steady_clock::now()-begin).count();
  std::cout<<"level="<<level+1<<" states="<<work.size()<<" moves="<<moves<<" length="<<lenCuts<<" sep="<<sepCuts<<" fullsep="<<fullCuts<<" redundant="<<redCuts<<" projection="<<projCuts<<" links="<<linkCuts<<" factor="<<factorCuts<<" open="<<open<<" distinct="<<next.size()<<" wires="<<wires.size()<<" sec="<<sec<<std::endl;
  work=std::move(next);
  checkpoint(level+1,work);
 }
 dumpWires();wireTrace.close();if(!wireTrace)throw std::runtime_error("wire trace close failure");
 if(fullSeparation){std::ofstream out("signed-collision-pairs.txt");for(auto&[pair,count]:pairCounts)out<<pair.first<<" "<<pair.second<<" "<<count<<"\n";out.close();if(!out)throw std::runtime_error("collision summary write/close failure");}
}
