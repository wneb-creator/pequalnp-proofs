#include "probe-data.hpp"
constexpr bool signedMode=false;
#include "factor-cut.hpp"
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
std::unordered_map<Word,int,WHash> wireIds;
int intern(const Word&w,int op=-1,int a=-1,int b=-1,int var=-1){auto[it,ok]=wireIds.emplace(w,wires.size());if(ok)wires.push_back({w,coverage(w),op,a,b,var});return it->second;}
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
 for(size_t pi=0;pi<poolData.size();pi++){
  auto&p=poolData[pi];
  uint32_t cm=0;
  std::vector<Word> masked;
  for(size_t i=0;i<ws.size();i++){Word w=band(wires[ws[i]].word,p.domain);masked.push_back(w);if(w==zero||w==p.domain)cm|=1U<<i;}
  int maxPaid=p.bound+std::popcount(cm)-(cap-1);
  if(maxPaid<0)continue;
  std::vector<std::pair<std::vector<Word>,int>> banks{{p.wires,0}};
  for(size_t si=0;si<prefix.size()&&(allPaid||si==0);si++){
   auto s=prefix[si];Word a=band(wires[s.a].word,p.domain),b=band(wires[s.b].word,p.domain),z=binary(s.op,a,b);
   size_t sz=banks.size();
   for(size_t i=0;i<sz;i++)if(banks[i].second<maxPaid&&contains(banks[i].first,a)&&contains(banks[i].first,b)&&!contains(banks[i].first,z)){
    auto bank=banks[i];bank.first.push_back(z);if(signedMode)bank.first.push_back(band(bneg(z),p.domain));bank.second++;banks.push_back(std::move(bank));
   }
  }
  for(auto&[vals,paid]:banks){
   uint32_t un=0;
   for(size_t i=0;i<ws.size();i++){
    Word v=masked[i];
    if(!contains(vals,v))un|=1U<<i;
   }
   if(std::popcount(un)<=2)answer.push_back({int(pi),paid,std::popcount(cm),un,cm,std::move(vals)});
  }
 }
 return answer;
}
#include "compact-pools.hpp"
struct VecHash{size_t operator()(const std::vector<int>&w)const{size_t h=0;for(int x:w)h^=size_t(x)+0x9e3779b97f4a7c15ULL+(h<<6)+(h>>2);return h;}};
struct State{std::vector<int> ws;std::vector<Step> prefix;};
std::pair<int,int> collision(const std::vector<int>&ws){
 std::vector<int> representative(1U<<ws.size(),-1);
 for(int r=0;r<1024;r++){
  unsigned profile=0;for(size_t i=0;i<ws.size();i++)if(bit(wires[ws[i]].word,r))profile|=1U<<i;
  int s=representative[profile];
  if(s>=0&&bit(target,r)!=bit(target,s))return bit(target,r)?std::pair(r,s):std::pair(s,r);
  representative[profile]=r;
 }
 return {-1,-1};
}
int main(int argc,char**argv){
 int depth=argc>1?std::stoi(argv[1]):3;bool allPaid=argc<3||std::stoi(argv[2]);
 int resumeLevel=argc>4?std::stoi(argv[4]):0;
 std::string resumeDir=argc>5?argv[5]:"";
 if(resumeLevel&&resumeDir.empty())throw std::runtime_error("resume needs separate source directory");
 if(resumeLevel&&std::filesystem::weakly_canonical(resumeDir)==std::filesystem::current_path())throw std::runtime_error("resume source equals output directory");
 bool factor=!signedMode&&(argc<4||std::stoi(argv[3]));
 bool fullSeparation=signedMode&&(argc<5||std::stoi(argv[4]));
 std::map<std::pair<int,int>,int> pairCounts;
 std::ofstream factorStates("factor-states.bin",std::ios::binary);
 std::ofstream wireTrace("wires.bin",std::ios::binary);
 factorStates.exceptions(std::ios::failbit|std::ios::badbit);
 wireTrace.exceptions(std::ios::failbit|std::ios::badbit);
 size_t writtenWires=0;
 auto dumpWires=[&](){for(;writtenWires<wires.size();writtenWires++){auto&w=wires[writtenWires];wireTrace.write(reinterpret_cast<const char*>(w.word.data()),128);int origin[4]={w.op,w.a,w.b,w.var};wireTrace.write(reinterpret_cast<const char*>(origin),16);}wireTrace.flush();};
 auto checkpoint=[&](int level,const std::vector<State>&states){dumpWires();factorStates.flush();std::ofstream out("frontier-"+std::to_string(level)+".bin",std::ios::binary);out.exceptions(std::ios::failbit|std::ios::badbit);uint64_t count=states.size(),nw=wires.size();out.write(reinterpret_cast<char*>(&nw),8);out.write(reinterpret_cast<char*>(&count),8);for(auto&s:states){uint32_t n=s.ws.size(),d=s.prefix.size();out.write(reinterpret_cast<char*>(&n),4);out.write(reinterpret_cast<char*>(&d),4);out.write(reinterpret_cast<const char*>(s.ws.data()),4*n);out.write(reinterpret_cast<const char*>(s.prefix.data()),12*d);}out.close();};
 auto begin=std::chrono::steady_clock::now();
 std::vector<int> base;for(size_t i=0;i<rawInputs.size();i++)base.push_back(intern(rawInputs[i],-1,-1,-1,int(i)));
 for(auto&p:automorphisms){std::array<int,1024> rp;for(int r=0;r<1024;r++){int s=0;for(int i=0;i<10;i++)if(r>>p[i]&1)s|=1<<i;rp[r]=s;}rowPerms.push_back(rp);}
 makeEnds();
 std::unordered_map<std::vector<int>,int,VecHash> known;
 for(auto&[k,state]:knownStates){std::vector<int> ws;for(auto&w:state)ws.push_back(intern(w));auto key=canonical(ws);auto[it,ok]=known.emplace(key,k);if(!ok&&it->second<k)it->second=k;}
 std::sort(base.begin(),base.end());
 std::vector<State> work{{base,{}}};Cov all=covfull();
 if(resumeLevel){
  std::ifstream front(resumeDir+"/frontier-"+std::to_string(resumeLevel)+".bin",std::ios::binary);
  uint64_t nw=0,count=0;front.read(reinterpret_cast<char*>(&nw),8);front.read(reinterpret_cast<char*>(&count),8);
  if(!front||nw>100000000||count>100000000)throw std::runtime_error("badfrontierheader");
  std::ifstream sourceWires(resumeDir+"/wires.bin",std::ios::binary);
  for(uint64_t id=0;id<nw;id++){Word w;int origin[4];
   if(!sourceWires.read(reinterpret_cast<char*>(w.data()),128))throw std::runtime_error("truncated wire table");
   if(!sourceWires.read(reinterpret_cast<char*>(origin),16))throw std::runtime_error("truncated wire origin");
   if(origin[3]>=0){if(origin[3]>=10||w!=rawInputs[origin[3]])throw std::runtime_error("inputorigin");}
   else if(origin[0]>=0){if(origin[0]>1||origin[1]<0||origin[2]<0||uint64_t(origin[1])>=id||uint64_t(origin[2])>=id||binary(origin[0],wires[origin[1]].word,wires[origin[2]].word)!=w)throw std::runtime_error("gateorigin");}
   else throw std::runtime_error("unverified wire origin");
   if(intern(w,origin[0],origin[1],origin[2],origin[3])!=int(id))throw std::runtime_error("wireid");}
  if(!sourceWires)throw std::runtime_error("badwirefile");
  work.clear();work.reserve(count);
  for(uint64_t i=0;i<count;i++){uint32_t n=0,d=0;
   if(!front.read(reinterpret_cast<char*>(&n),4)||!front.read(reinterpret_cast<char*>(&d),4))throw std::runtime_error("truncated state header");
   if(n>31||d!=uint32_t(resumeLevel))throw std::runtime_error("frontierwidth");
   State s;s.ws.resize(n);s.prefix.resize(d);
   if(!front.read(reinterpret_cast<char*>(s.ws.data()),4*n)||!front.read(reinterpret_cast<char*>(s.prefix.data()),12*d))throw std::runtime_error("truncated state payload");
   for(int v:s.ws)if(v<0||uint64_t(v)>=nw)throw std::runtime_error("statewireid");
   if(!std::is_sorted(s.ws.begin(),s.ws.end())||std::adjacent_find(s.ws.begin(),s.ws.end())!=s.ws.end())throw std::runtime_error("noncanonical state list");
   for(auto&t:s.prefix)if(t.op<0||t.op>1||t.a<0||t.b<0||uint64_t(t.a)>=nw||uint64_t(t.b)>=nw)throw std::runtime_error("prefixid");
   work.push_back(std::move(s));}
  if(!front)throw std::runtime_error("badfrontierfile");
 }
 checkpoint(resumeLevel,work);
 for(int level=resumeLevel;level<depth;level++){
  uint64_t moves=0,lenCuts=0,sepCuts=0,redCuts=0,projCuts=0,linkCuts=0,factorCuts=0,fullCuts=0,open=0;
  int k=19-level;
  std::unordered_map<std::vector<int>,size_t,VecHash> seen;
  std::vector<State> next;
  size_t done=0;
  CompactResult specs;
  std::array<int,512> bucketHeads;
  std::vector<int> nextSpec;
  for(auto&state:work){
   const auto&ws=state.ws;
   for(int w:ws)if(wires[w].word==target){std::cerr<<"TARGET PRESENT at level "<<level+1<<" width "<<ws.size()<<std::endl;return 4;}
   if(fullSeparation){auto pair=collision(ws);if(pair.first>=0){fullCuts++;pairCounts[pair]++;continue;}}
   if(factor&&k<=int(ws.size())){
    std::vector<Word> words;for(int w:ws)words.push_back(wires[w].word);
    if(H8Factor::cut(words,k)){
     factorCuts++;
     uint32_t cap=k,count=ws.size();factorStates.write(reinterpret_cast<char*>(&cap),4);factorStates.write(reinterpret_cast<char*>(&count),4);factorStates.write(reinterpret_cast<const char*>(ws.data()),4*count);
     continue;
    }
   }
   compactSpecs(ws,state.prefix,allPaid,k,specs);
   bucketHeads.fill(-1);nextSpec.resize(specs.specs.size());
   auto bucketIndex=[&](uint32_t mask){if(!mask)return 0;int a=std::countr_zero(mask);mask&=mask-1;if(!mask)return 1+a;int b=std::countr_zero(mask);return 1+int(ws.size())+b*(b-1)/2+a;};
   for(size_t si=specs.specs.size();si-->0;){int bucket=bucketIndex(specs.specs[si].unavailable);nextSpec[si]=bucketHeads[bucket];bucketHeads[bucket]=int(si);}
   for(size_t i=0;i<ws.size();i++)for(size_t j=i+1;j<ws.size();j++)for(int op=0;op<(signedMode?4:2);op++){
    int a=ws[i],b=ws[j];Word zw=binary(op,wires[a].word,wires[b].word);int zi=intern(zw,op,a,b);Cov cz=wires[zi].cov;
    for(int keeps=0;keeps<4;keeps++){
     moves++;bool ka=keeps&1,kb=keeps&2;uint32_t deleted=(ka?0:1U<<i)|(kb?0:1U<<j);
     if(ws.size()+1-std::popcount(deleted)>size_t(k)){lenCuts++;continue;}
     Cov cov=cz;for(size_t l=0;l<ws.size();l++)if(!(deleted>>l&1))cov=cor(cov,wires[ws[l]].cov);
     if(cov!=all){sepCuts++;continue;}
     if(zw==zero||zw==bneg(zero)||std::find(ws.begin(),ws.end(),zi)!=ws.end()){redCuts++;continue;}
     bool cut=false;
     int buckets[4]={0,0,0,0},nb=1;
     if(!ka)buckets[nb++]=1+int(i);if(!kb)buckets[nb++]=1+int(j);
     if(!ka&&!kb)buckets[nb++]=bucketIndex((1U<<i)|(1U<<j));
     for(int bi=0;bi<nb&&!cut;bi++)for(int sid=bucketHeads[buckets[bi]];sid>=0;sid=nextSpec[sid]){
      auto&s=specs.specs[sid];
      auto&p=poolData[s.pool];int hi=p.bound+s.constants-std::popcount(s.constantmask&deleted),lo=k-1+s.paid;
      if(lo>hi)continue;
      auto endpoints=ends[s.pool];bool constant=bit(zw,endpoints.lo)||!bit(zw,endpoints.hi);
      if(constant){cut=true;break;}
      if(lo==hi)continue;
      if(s.unavailable==0&&lo+1<hi){cut=true;break;}
      Word zr=band(zw,p.domain);bool av=contains(p.wires,zr);
      for(size_t t=0;!av&&t<specs.depth;t++)if((s.selected>>t&1)&&specs.projected[size_t(s.pool)*specs.depth+t]==zr)av=true;
      if(av){cut=true;break;}
     }
     if(cut){projCuts++;continue;}
     std::vector<int> child;for(size_t l=0;l<ws.size();l++)if(!(deleted>>l&1))child.push_back(ws[l]);child.push_back(zi);std::sort(child.begin(),child.end());
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
 dumpWires();
 factorStates.close();
 wireTrace.close();
 if(fullSeparation){std::ofstream out("signed-collision-pairs.txt");for(auto&[pair,count]:pairCounts)out<<pair.first<<" "<<pair.second<<" "<<count<<"\n";}
}
