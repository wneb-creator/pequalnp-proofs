#ifdef SIGNED_MODE
#include "signed-probe-data.hpp"
constexpr bool signedMode=true;
#else
#include "probe-data.hpp"
constexpr bool signedMode=false;
#endif
#include "factor-cut.hpp"
#include <algorithm>
#include <bit>
#include <chrono>
#include <iostream>
#include <iomanip>
#include <map>
#include <unordered_map>
#include <unordered_set>

struct WHash { size_t operator()(const Word&w) const {size_t h=0;for(auto x:w)h^=(x+0x9e3779b97f4a7c15ULL+(h<<6)+(h>>2));return h;} };
Word band(const Word&a,const Word&b){Word w;for(int i=0;i<8;i++)w[i]=a[i]&b[i];return w;}
Word bor(const Word&a,const Word&b){Word w;for(int i=0;i<8;i++)w[i]=a[i]|b[i];return w;}
Word bneg(const Word&a){Word w;for(int i=0;i<8;i++)w[i]=~a[i];return w;}
Word binary(int op,const Word&a,const Word&b){return op==0?band(a,b):op==1?bor(a,b):op==2?band(a,bneg(b)):band(bneg(a),b);}
bool bit(const Word&w,int n){return (w[n/64]>>(n%64))&1;}
Word zero{};
using Cov=std::array<uint64_t,3>;
Cov coverage(const Word&w){Cov c{};for(size_t i=0;i<boundaryPairs.size();i++){auto[p,n]=boundaryPairs[i];if(signedMode?(bit(w,p)!=bit(w,n)):(bit(w,p)&&!bit(w,n)))c[i/64]|=1ULL<<(i%64);}return c;}
Cov covfull(){Cov c{};for(size_t i=0;i<boundaryPairs.size();i++)c[i/64]|=1ULL<<(i%64);return c;}
Cov cor(Cov a,const Cov&b){for(int i=0;i<3;i++)a[i]|=b[i];return a;}
struct Wire{Word word;Cov cov;};
std::vector<Wire>wires;
std::unordered_map<Word,int,WHash> wireIds;
int intern(const Word&w){auto[it,ok]=wireIds.emplace(w,wires.size());if(ok)wires.push_back({w,coverage(w)});return it->second;}
std::vector<std::array<int,512>> rowPerms;
std::map<std::pair<int,int>,int> imageIds;
int imageWire(int id,int p){
 if(p==0)return id;
 auto key=std::make_pair(id,p);auto it=imageIds.find(key);if(it!=imageIds.end())return it->second;
 Word w{};for(int r=0;r<512;r++)if(bit(wires[id].word,rowPerms[p][r]))w[r/64]|=1ULL<<(r%64);
 int mapped=intern(w);imageIds.emplace(key,mapped);return mapped;
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
std::vector<Spec> makeSpecs(const std::vector<int>&ws,const std::vector<Step>&prefix,bool allPaid){
 std::vector<Spec> answer;
 for(size_t pi=0;pi<poolData.size();pi++){
  auto&p=poolData[pi];
  std::vector<std::pair<std::vector<Word>,int>> banks{{p.wires,0}};
  for(size_t si=0;si<prefix.size()&&(allPaid||si==0);si++){
   auto s=prefix[si];Word a=band(wires[s.a].word,p.domain),b=band(wires[s.b].word,p.domain),z=binary(s.op,a,b);
   size_t sz=banks.size();
   for(size_t i=0;i<sz;i++)if(contains(banks[i].first,a)&&contains(banks[i].first,b)&&!contains(banks[i].first,z)){
    auto bank=banks[i];bank.first.push_back(z);if(signedMode)bank.first.push_back(band(bneg(z),p.domain));bank.second++;banks.push_back(std::move(bank));
   }
  }
  for(auto&[vals,paid]:banks){
   uint32_t un=0,cm=0;
   for(size_t i=0;i<ws.size();i++){
    Word v=band(wires[ws[i]].word,p.domain);
    if(v==zero||v==p.domain)cm|=1U<<i;
    if(!contains(vals,v))un|=1U<<i;
   }
   if(std::popcount(un)<=2)answer.push_back({int(pi),paid,std::popcount(cm),un,cm,std::move(vals)});
  }
 }
 return answer;
}
struct VecHash{size_t operator()(const std::vector<int>&w)const{size_t h=0;for(int x:w)h^=size_t(x)+0x9e3779b97f4a7c15ULL+(h<<6)+(h>>2);return h;}};
struct State{std::vector<int> ws;std::vector<Step> prefix;};
std::pair<int,int> collision(const std::vector<int>&ws){
 std::vector<int> representative(1U<<ws.size(),-1);
 for(int r=0;r<512;r++){
  unsigned profile=0;for(size_t i=0;i<ws.size();i++)if(bit(wires[ws[i]].word,r))profile|=1U<<i;
  int s=representative[profile];
  if(s>=0&&bit(target,r)!=bit(target,s))return bit(target,r)?std::pair(r,s):std::pair(s,r);
  representative[profile]=r;
 }
 return {-1,-1};
}
int main(int argc,char**argv){
 int depth=argc>1?std::stoi(argv[1]):3;bool allPaid=argc<3||std::stoi(argv[2]);
 bool factor=!signedMode&&(argc<4||std::stoi(argv[3]));
 bool fullSeparation=signedMode&&(argc<5||std::stoi(argv[4]));
 std::map<std::pair<int,int>,int> pairCounts;
 std::ofstream factorStates(signedMode?"signed-factor-states.txt":"factor-states.txt");
 auto knownStates=loadKnownStates(argc>5?argv[5]:(signedMode?"signed-known-states.bin":"known-states.bin"));
 auto begin=std::chrono::steady_clock::now();
 std::vector<int> base;for(auto&w:rawInputs)base.push_back(intern(w));
 for(auto&p:automorphisms){std::array<int,512> rp;for(int r=0;r<512;r++){int s=0;for(int i=0;i<9;i++)if(r>>p[i]&1)s|=1<<i;rp[r]=s;}rowPerms.push_back(rp);}
 std::unordered_map<std::vector<int>,int,VecHash> known;
 for(auto&[k,state]:knownStates){std::vector<int> ws;for(auto&w:state)ws.push_back(intern(w));auto key=canonical(ws);auto[it,ok]=known.emplace(key,k);if(!ok&&it->second<k)it->second=k;}
 int z=intern(bor(rawInputs[4],rawInputs[6]));base.push_back(z);std::sort(base.begin(),base.end());
 std::vector<State> work{{base,{{1,4,6}}}};Cov all=covfull();
 for(int level=0;level<depth;level++){
  uint64_t moves=0,lenCuts=0,sepCuts=0,redCuts=0,projCuts=0,linkCuts=0,factorCuts=0,fullCuts=0,open=0;
  int k=(signedMode?14:15)-level;
  std::unordered_map<std::vector<int>,size_t,VecHash> seen;
  std::vector<State> next;
  size_t done=0;
  for(auto&state:work){
   const auto&ws=state.ws;
   for(int w:ws)if(wires[w].word==target){std::cerr<<"TARGET PRESENT at level "<<level+1<<" width "<<ws.size()<<std::endl;return 4;}
   if(fullSeparation){auto pair=collision(ws);if(pair.first>=0){fullCuts++;pairCounts[pair]++;continue;}}
   if(factor&&k<=int(ws.size())){
    std::vector<Word> words;for(int w:ws)words.push_back(wires[w].word);
    if(H8Factor::cut(words,k)){
     factorCuts++;
     factorStates<<std::dec<<k<<" "<<ws.size();for(auto&w:words){factorStates<<" ";for(int j=7;j>=0;j--)factorStates<<std::hex<<std::setfill('0')<<std::setw(16)<<w[j];}factorStates<<"\n";
     continue;
    }
   }
   auto specs=makeSpecs(ws,state.prefix,allPaid);
   for(size_t i=0;i<ws.size();i++)for(size_t j=i+1;j<ws.size();j++)for(int op=0;op<(signedMode?4:2);op++){
    int a=ws[i],b=ws[j];Word zw=binary(op,wires[a].word,wires[b].word);if(zw==target){std::cerr<<"TARGET GENERATED at level "<<level+1<<std::endl;return 4;}int zi=intern(zw);Cov cz=wires[zi].cov;
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
      bool av=constant||contains(s.values,zr);
      if(lo+!av<hi+constant&&(av||!(s.unavailable&((1U<<i)|(1U<<j))))){cut=true;break;}
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
 }
 if(fullSeparation){std::ofstream out("signed-collision-pairs.txt");for(auto&[pair,count]:pairCounts)out<<pair.first<<" "<<pair.second<<" "<<count<<"\n";}
}
